import BanachGeometry.WeakSequences.TailReduction
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! R6 weak-tail proof support. Bounded coordinate functionals are summed
pointwise with an absolute-summability proof. This does not assert convergence
of the series of functionals in operator norm. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace L1DualBlocks

variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

theorem summable_norm_eval (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (x : L1Sum V) : Summable (fun i => ‖φ i (x i)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  · intro i
    calc
      ‖φ i (x i)‖ ≤ ‖φ i‖ * ‖x i‖ := (φ i).le_opNorm _
      _ ≤ 1 * ‖x i‖ := mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg _)
      _ = ‖x i‖ := one_mul _
  · exact l1_summable x

theorem summable_eval (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (x : L1Sum V) : Summable (fun i => φ i (x i)) :=
  (summable_norm_eval V φ hφ x).of_norm

theorem norm_eval_sum_le (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (x : L1Sum V) : ‖∑' i, φ i (x i)‖ ≤ ‖x‖ := by
  calc
    ‖∑' i, φ i (x i)‖ ≤ ∑' i, ‖φ i (x i)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_eval V φ hφ x)
    _ ≤ ∑' i, ‖x i‖ := by
      apply Summable.tsum_le_tsum
      · intro i
        exact ((φ i).le_opNorm _).trans
          ((mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg _)).trans_eq (one_mul _))
      · exact summable_norm_eval V φ hφ x
      · exact l1_summable x
    _ = ‖x‖ := (l1_norm_eq_tsum x).symm

def functional (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1) : L1Sum V →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑' i, φ i (x i)
     map_add' := by
       intro x y
       simp only [lp.coeFn_add, Pi.add_apply, map_add]
       exact (summable_eval V φ hφ x).tsum_add (summable_eval V φ hφ y)
     map_smul' := by
       intro a x
       simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
       rw [tsum_mul_left] } : L1Sum V →ₗ[ℝ] ℝ).mkContinuous 1
    (fun x => by
      change ‖∑' i, φ i (x i)‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_eval_sum_le V φ hφ x)

@[simp] theorem functional_apply (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (x : L1Sum V) : functional V φ hφ x = ∑' i, φ i (x i) := rfl

theorem norm_functional_le (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1) :
    ‖functional V φ hφ‖ ≤ 1 :=
  (functional V φ hφ).opNorm_le_bound zero_le_one
    (fun x => by
      change ‖∑' i, φ i (x i)‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_eval_sum_le V φ hφ x)

theorem exists_norming_family (x : L1Sum V) :
    ∃ φ : ∀ i, V i →L[ℝ] ℝ, (∀ i, ‖φ i‖ ≤ 1) ∧ (∀ i, φ i (x i) = ‖x i‖) := by
  choose φ hφ heval using fun i => exists_dual_vector'' ℝ (x i)
  exact ⟨φ, hφ, heval⟩

theorem exists_norming_functional (x : L1Sum V) :
    ∃ f : L1Sum V →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ f x = ‖x‖ := by
  obtain ⟨φ, hφ, heval⟩ := exists_norming_family V x
  refine ⟨functional V φ hφ, norm_functional_le V φ hφ, ?_⟩
  rw [functional_apply, l1_norm_eq_tsum]
  exact tsum_congr heval

def mask (φ : ∀ i, V i →L[ℝ] ℝ) (a b : ℕ) (i : ℕ) : V i →L[ℝ] ℝ :=
  if a ≤ i ∧ i < b then φ i else 0

theorem norm_mask_le (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (a b i : ℕ) : ‖mask V φ a b i‖ ≤ 1 := by
  unfold mask
  split_ifs
  · exact hφ i
  · simp

/-- A finite block functional, represented by the same absolutely summable
construction that will later support the infinite disjoint-block functional. -/
def blockFunctional (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (a b : ℕ) : L1Sum V →L[ℝ] ℝ :=
  functional V (mask V φ a b) (norm_mask_le V φ hφ a b)

theorem blockFunctional_apply (φ : ∀ i, V i →L[ℝ] ℝ) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (a b : ℕ) (x : L1Sum V) :
    blockFunctional V φ hφ a b x = ∑ i ∈ Finset.Ico a b, φ i (x i) := by
  rw [blockFunctional, functional_apply]
  calc
    (∑' i, mask V φ a b i (x i)) = ∑ i ∈ Finset.Ico a b, mask V φ a b i (x i) := by
      apply tsum_eq_sum
      intro i hi
      have hnot : ¬ (a ≤ i ∧ i < b) := by simpa only [Finset.mem_Ico] using hi
      simp only [mask, if_neg hnot, ContinuousLinearMap.zero_apply]
    _ = ∑ i ∈ Finset.Ico a b, φ i (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [mask, if_pos (Finset.mem_Ico.mp hi)]

theorem blockFunctional_norming (x : L1Sum V) (a b : ℕ) :
    ∃ f : L1Sum V →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧
      f x = ∑ i ∈ Finset.Ico a b, ‖x i‖ := by
  obtain ⟨φ, hφ, heval⟩ := exists_norming_family V x
  refine ⟨blockFunctional V φ hφ a b,
    norm_functional_le V (mask V φ a b) (norm_mask_le V φ hφ a b), ?_⟩
  rw [blockFunctional_apply]
  exact Finset.sum_congr rfl (fun i _ => heval i)

/-- The final contradiction once recursive block selection has supplied one
bounded functional that stays positively separated on a subsequence. -/
theorem not_weakNull_of_separated_functional {u : ℕ → L1Sum V}
    (s : ℕ → ℕ) (hs : StrictMono s) (f : L1Sum V →L[ℝ] ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hsep : ∀ j, δ ≤ f (u (s j))) : ¬ WeakNull u := by
  intro hu
  have ht := (hu f).comp hs.tendsto_atTop
  have he : ∀ᶠ j in atTop, f (u (s j)) < δ :=
    ht.eventually (eventually_lt_nhds hδ)
  obtain ⟨j, hj⟩ := he.exists
  exact (hsep j).not_gt hj

end L1DualBlocks
end BanachGeometry
