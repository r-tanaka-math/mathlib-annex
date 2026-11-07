import BanachGeometry.NoC0.BPSeparation
import BanachGeometry.AlmostIsometric.ApproximationParameters

/-! Simultaneous subsequence/functional construction for BP-basis.
The next step works for ANY finite prefix, so recursion uses no unproved
basic-sequence or extension assumption. All choices have proved witnesses.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace BP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def budget (j : ℕ) : ℝ := ApproximationParameters.weight 2 j
theorem budget_pos (j : ℕ) : 0 < budget j := ApproximationParameters.weight_pos 2 j
theorem summable_budget : Summable budget := ApproximationParameters.weight_summable 2
theorem tsum_budget : (∑' j, budget j) = 1/8 := by
  change (∑' j, ApproximationParameters.weight 2 j) = 1/8
  rw [ApproximationParameters.weights_sum]
  norm_num [ApproximationParameters.theta]

abbrev SelectionPair (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℕ × (E →L[ℝ] ℝ)

def StepProperty (u : ℕ → E) (δ : ℝ) (n : ℕ)
    (p : Fin n → SelectionPair E) (z : SelectionPair E) : Prop :=
  (∀ i, (p i).1 < z.1) ∧ ‖z.2‖ ≤ 1 ∧ δ/4 ≤ z.2 (u z.1) ∧
    (∀ i, z.2 (u (p i).1) = 0) ∧
    (∀ i, |(p i).2 (u z.1)| ≤ δ * budget n)

theorem exists_step (u : ℕ → E) (hu : WeakNull u) (δ : ℝ) (hδ : 0 < δ)
    (hbad : ∀ N : ℕ, ∃ k, N ≤ k ∧ δ ≤ ‖u k‖)
    (n : ℕ) (p : Fin n → SelectionPair E) : ∃ z, StepProperty u δ n p z := by
  classical
  let v : Fin n → E := fun i => u (p i).1
  let V := Submodule.span ℝ (Set.range v)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_norm_sub_ge_of_mem_finiteDimensional u hu V δ hδ)
  have hsmall : ∀ᶠ k in atTop, ∀ i ∈ (Finset.univ : Finset (Fin n)),
      |(p i).2 (u k)| < δ * budget n := by
    apply (Filter.eventually_all_finset _).mpr
    intro i hi
    simpa only [Real.norm_eq_abs,norm_zero] using
      (hu (p i).2).norm.eventually (eventually_lt_nhds
        (by simpa only [norm_zero] using mul_pos hδ (budget_pos n)))
  obtain ⟨N₁,hN₁⟩ := Filter.eventually_atTop.mp hsmall
  let N := max N₀ (max N₁ ((Finset.univ.sup (fun i : Fin n => (p i).1)) + 1))
  obtain ⟨k,hNk,hkδ⟩ := hbad N
  have hk₀ : N₀ ≤ k := (le_max_left _ _).trans hNk
  have hk₁ : N₁ ≤ k := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hNk
  have hkp (i : Fin n) : (p i).1 < k := by
    have hi := Finset.le_sup (f := fun i : Fin n => (p i).1) (Finset.mem_univ i)
    have hn : (Finset.univ.sup (fun i : Fin n => (p i).1)) + 1 ≤ k :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hNk
    omega
  obtain ⟨f,hf,hzero,hdiag⟩ := exists_annihilating_functional V (u k) (δ/4) (hN₀ k hk₀ hkδ)
  refine ⟨(k,f),hkp,hf,hdiag,?_,?_⟩
  · intro i
    exact hzero _ (Submodule.subset_span (Set.mem_range_self i))
  · intro i
    exact (hN₁ k hk₁ i (Finset.mem_univ i)).le

variable (u : ℕ → E) (hu : WeakNull u) (δ : ℝ) (hδ : 0 < δ)
    (hbad : ∀ N : ℕ, ∃ k, N ≤ k ∧ δ ≤ ‖u k‖)

def chooseStep (n : ℕ) (p : Fin n → SelectionPair E) : SelectionPair E :=
  Classical.choose (exists_step u hu δ hδ hbad n p)
theorem chooseStep_spec (n : ℕ) (p : Fin n → SelectionPair E) :
    StepProperty u δ n p (chooseStep u hu δ hδ hbad n p) :=
  Classical.choose_spec (exists_step u hu δ hδ hbad n p)

def prefixes : ℕ → (ℕ → SelectionPair E)
  | 0 => fun _ => (0,0)
  | n+1 => Function.update (prefixes n) n
      (chooseStep u hu δ hδ hbad n (fun i => prefixes n i.val))

def selected (n : ℕ) : SelectionPair E := prefixes u hu δ hδ hbad (n+1) n

theorem prefixes_eq_selected {i n : ℕ} (hi : i < n) :
    prefixes u hu δ hδ hbad n i = selected u hu δ hδ hbad i := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hi)
  induction m with
  | zero => rfl
  | succ m ih =>
    change Function.update (prefixes u hu δ hδ hbad (i+1+m)) (i+1+m) _ i = _
    rw [Function.update_of_ne (by omega : i ≠ i+1+m)]
    exact ih (by omega)

theorem selected_spec (n : ℕ) :
    StepProperty u δ n (fun i => selected u hu δ hδ hbad i.val)
      (selected u hu δ hδ hbad n) := by
  have hs := chooseStep_spec u hu δ hδ hbad n
    (fun i => prefixes u hu δ hδ hbad n i.val)
  have hc : selected u hu δ hδ hbad n = chooseStep u hu δ hδ hbad n
      (fun i => prefixes u hu δ hδ hbad n i.val) := by
    change Function.update _ n _ n = _
    exact Function.update_self _ _ _
  rw [← hc] at hs
  have hp (i : Fin n) : prefixes u hu δ hδ hbad n i.val = selected u hu δ hδ hbad i.val :=
    prefixes_eq_selected u hu δ hδ hbad i.isLt
  simpa only [hp] using hs

structure TriangularData (u : ℕ → E) (δ : ℝ) where
  k : ℕ → ℕ
  f : ℕ → E →L[ℝ] ℝ
  strictMono_k : StrictMono k
  norm_f_le : ∀ i, ‖f i‖ ≤ 1
  diag : ∀ i, δ/4 ≤ f i (u (k i))
  lower_zero : ∀ i j, j < i → f i (u (k j)) = 0
  upper_small : ∀ i j, i < j → |f i (u (k j))| ≤ δ * budget j

def triangularData : TriangularData u δ where
  k i := (selected u hu δ hδ hbad i).1
  f i := (selected u hu δ hδ hbad i).2
  strictMono_k i j hij := (selected_spec u hu δ hδ hbad j).1 ⟨i,hij⟩
  norm_f_le i := (selected_spec u hu δ hδ hbad i).2.1
  diag i := (selected_spec u hu δ hδ hbad i).2.2.1
  lower_zero i j hji := (selected_spec u hu δ hδ hbad i).2.2.2.1 ⟨j,hji⟩
  upper_small i j hij := (selected_spec u hu δ hδ hbad j).2.2.2.2 ⟨i,hij⟩

end BP
end BanachGeometry
