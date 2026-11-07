import BanachGeometry.SequenceSpaces.SumReindex
import Mathlib.Analysis.Normed.Group.Constructions

open scoped ENNReal

/-! Finite collections of countable heterogeneous rows. The ℓ₁ norm
lies between each row norm and the sum of the row norms. The c₀ norm is
the finite maximum. Includes the empty finite family.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace SumFinite
variable {q : ℕ} (V : Fin q → ℕ → Type*)
    [∀ r j, NormedAddCommGroup (V r j)] [∀ r j, NormedSpace ℝ (V r j)]
abbrev Total := fun p : Fin q × ℕ => V p.1 p.2

def l1Collect (x : ∀ r, L1Sum (V r)) : L1Sum (Total V) :=
  ⟨fun p => x p.1 p.2, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    have hs : Summable (fun p : Fin q × ℕ => ‖x p.1 p.2‖) :=
      (summable_prod_of_nonneg (fun p => norm_nonneg (x p.1 p.2))).mpr
        ⟨fun r => l1_summable (x r), (hasSum_fintype _).summable⟩
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hs⟩

def l1Row (r : Fin q) (z : L1Sum (Total V)) : L1Sum (V r) :=
  ⟨fun j => z (r,j), by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    have hs := (l1_summable z).comp_injective (show Function.Injective (fun j : ℕ => (r,j)) from
      fun j k h => congrArg Prod.snd h)
    simpa only [Function.comp_def, ENNReal.toReal_one, Real.rpow_one] using hs⟩

theorem norm_l1Row_le (r : Fin q) (z : L1Sum (Total V)) : ‖l1Row V r z‖ ≤ ‖z‖ := by
  classical
  rw [l1_norm_eq_tsum]
  apply Real.tsum_le_of_sum_le (fun j => norm_nonneg _)
  intro s
  let e : ℕ ↪ Fin q × ℕ := ⟨fun j => (r,j), fun j k h => congrArg Prod.snd h⟩
  have he := (l1_summable z).sum_le_tsum (s.map e) (fun p hp => norm_nonneg (z p))
  rw [← l1_norm_eq_tsum] at he
  change (∑ j ∈ s, ‖z (r, j)‖) ≤ ‖z‖
  rw [Finset.sum_map] at he
  change (∑ j ∈ s, ‖z (r, j)‖) ≤ ‖z‖ at he
  exact he

theorem norm_l1Collect_le_sum (x : ∀ r, L1Sum (V r)) :
    ‖l1Collect V x‖ ≤ ∑ r, ‖x r‖ := by
  classical
  rw [l1_norm_eq_tsum]
  apply Real.tsum_le_of_sum_le (fun p => norm_nonneg _)
  intro s
  let N := s.sup (fun p => p.2) + 1
  have hs : s ⊆ Finset.univ ×ˢ Finset.range N := by
    intro p hp
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_univ _, Finset.mem_range.mpr (by
      have h := Finset.le_sup (f := fun p : Fin q × ℕ => p.2) hp
      dsimp [N]; omega)⟩
  calc
    (∑ p ∈ s, ‖l1Collect V x p‖) ≤ ∑ p ∈ Finset.univ ×ˢ Finset.range N, ‖x p.1 p.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun p hp hps => norm_nonneg _)
    _ = ∑ r, ∑ j ∈ Finset.range N, ‖x r j‖ := Finset.sum_product _ _ _
    _ ≤ ∑ r, ‖x r‖ := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [← l1_norm_eq_tsum] using
        (l1_summable (x r)).sum_le_tsum (Finset.range N) (fun j hj => norm_nonneg _)

theorem norm_l1Collect_le (x : ∀ r, L1Sum (V r)) : ‖l1Collect V x‖ ≤ (q : ℝ) * ‖x‖ := by
  apply (norm_l1Collect_le_sum V x).trans
  calc
    (∑ r, ‖x r‖) ≤ ∑ r : Fin q, ‖x‖ := Finset.sum_le_sum (fun r hr => norm_le_pi_norm x r)
    _ = (q : ℝ) * ‖x‖ := by simp

def c0Collect (x : ∀ r, C0Sum (V r)) : C0Sum (Total V) :=
  C0Sum.ofBound (fun p => x p.1 p.2) (by
    classical
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he : ∀ᶠ m in atTop, ∀ r ∈ (Finset.univ : Finset (Fin q)), ‖x r m‖ < ε := by
      apply (Filter.eventually_all_finset _).mpr
      intro r hr
      exact (x r).null_atTop.eventually (eventually_lt_nhds hε)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
    filter_upwards [(Finset.univ ×ˢ Finset.range N).eventually_cofinite_notMem] with p hp
    have hn : N ≤ p.2 := by
      by_contra hbad
      apply hp
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩
    simpa only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] using
      hN p.2 hn p.1 (Finset.mem_univ _))
    ‖x‖ (fun p => ((x p.1).norm_apply_le p.2).trans (norm_le_pi_norm x p.1))

def c0Row (r : Fin q) (z : C0Sum (Total V)) : C0Sum (V r) :=
  C0Sum.ofBound (fun j => z (r,j)) (z.null.comp
    (show Function.Injective (fun j : ℕ => (r,j)) from fun j k h => congrArg Prod.snd h).tendsto_cofinite)
    ‖z‖ (fun j => z.norm_apply_le (r,j))

theorem norm_c0Collect_le (x : ∀ r, C0Sum (V r)) : ‖c0Collect V x‖ ≤ ‖x‖ :=
  C0Sum.norm_le (norm_nonneg _) (fun p => ((x p.1).norm_apply_le p.2).trans (norm_le_pi_norm x p.1))

theorem norm_c0Row_le (r : Fin q) (z : C0Sum (Total V)) : ‖c0Row V r z‖ ≤ ‖z‖ :=
  C0Sum.norm_le (norm_nonneg _) (fun j => z.norm_apply_le (r,j))

@[simp] theorem l1Row_collect (r : Fin q) (x : ∀ r, L1Sum (V r)) : l1Row V r (l1Collect V x) = x r := by
  apply lp.ext; rfl
@[simp] theorem l1Collect_rows (z : L1Sum (Total V)) : l1Collect V (fun r => l1Row V r z) = z := by
  apply lp.ext; rfl
@[simp] theorem c0Row_collect (r : Fin q) (x : ∀ r, C0Sum (V r)) : c0Row V r (c0Collect V x) = x r := by
  apply C0Sum.ext; intro j; rfl
@[simp] theorem c0Collect_rows (z : C0Sum (Total V)) : c0Collect V (fun r => c0Row V r z) = z := by
  apply C0Sum.ext; intro p; rfl

def l1CollectCLM : (∀ r, L1Sum (V r)) →L[ℝ] L1Sum (Total V) :=
  ({ toFun := l1Collect V
     map_add' := by intro x y; apply lp.ext; rfl
     map_smul' := by intro a x; apply lp.ext; rfl } : (∀ r, L1Sum (V r)) →ₗ[ℝ] L1Sum (Total V)).mkContinuous
      q (norm_l1Collect_le V)

def l1RowCLM (r : Fin q) : L1Sum (Total V) →L[ℝ] L1Sum (V r) :=
  ({ toFun := l1Row V r
     map_add' := by intro x y; apply lp.ext; rfl
     map_smul' := by intro a x; apply lp.ext; rfl } : L1Sum (Total V) →ₗ[ℝ] L1Sum (V r)).mkContinuous
      1 (by intro z; change ‖l1Row V r z‖ ≤ 1 * ‖z‖; simpa only [one_mul] using norm_l1Row_le V r z)

def c0CollectCLM : (∀ r, C0Sum (V r)) →L[ℝ] C0Sum (Total V) :=
  ({ toFun := c0Collect V
     map_add' := by intro x y; apply C0Sum.ext; intro p; rfl
     map_smul' := by intro a x; apply C0Sum.ext; intro p; rfl } : (∀ r, C0Sum (V r)) →ₗ[ℝ] C0Sum (Total V)).mkContinuous
      1 (by intro x; change ‖c0Collect V x‖ ≤ 1 * ‖x‖; simpa only [one_mul] using norm_c0Collect_le V x)

def c0RowCLM (r : Fin q) : C0Sum (Total V) →L[ℝ] C0Sum (V r) :=
  ({ toFun := c0Row V r
     map_add' := by intro x y; apply C0Sum.ext; intro j; rfl
     map_smul' := by intro a x; apply C0Sum.ext; intro j; rfl } : C0Sum (Total V) →ₗ[ℝ] C0Sum (V r)).mkContinuous
      1 (by intro z; change ‖c0Row V r z‖ ≤ 1 * ‖z‖; simpa only [one_mul] using norm_c0Row_le V r z)

end SumFinite
end BanachGeometry
