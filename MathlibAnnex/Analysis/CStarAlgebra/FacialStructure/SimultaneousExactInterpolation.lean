/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ProjectionApproximation

/-!
# Quantitative exact simultaneous self-adjoint interpolation

All corrections are selected in the original algebra. A constructed state
at stage `n` has restricted error less than `C / 6 / 2^n`; the next correction
has norm at most `C / 2 / 2^n`. Thus the corrections are absolutely summable.
Their sum is self-adjoint, has norm at most `2*C`, and has zero restricted
error in every fiber. The dependent subtype in the proof records the proved
finite-stage invariant; it does not assume an exact interpolant.

This generalizes the geometric-correction argument in the pinned
`ExactInterpolation` module, using the new simultaneous approximation
instead of applying an irreducible theorem to a reducible sum.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Coarse exact simultaneous interpolation with twice the common norm
budget. The displayed zero errors hold as operator identities after each
finite-dimensional orthogonal projection. -/
theorem exists_selfAdjoint_norm_le_two_mul_forall_sub_mul_starProjection_eq_zero
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * C ∧
      ∀ i, (T i - pi i a) * (E i).starProjection = 0 := by
  classical
  by_cases hzero : C = 0
  · subst C
    have hTzero (i : I) : T i = 0 := norm_eq_zero.mp (le_antisymm (hTC i) (norm_nonneg _))
    exact ⟨0, IsSelfAdjoint.zero A, by simp, by simp [hTzero]⟩
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  let P : ∀ i, H i →L[ℂ] H i := fun i => (E i).starProjection
  let State (n : ℕ) := {a : A // IsSelfAdjoint a ∧
    ∀ i, ‖(T i - pi i a) * P i‖ < C / 6 / 2 ^ n}
  obtain ⟨a0, ha0, ha0norm, ha0app⟩ :=
    exists_selfAdjoint_norm_le_forall_norm_sub_mul_starProjection_lt
      pi hirr hne E T hT C hC hTC (by positivity : 0 < C / 6)
  have ha0err (i : I) : ‖(T i - pi i a0) * P i‖ < C / 6 / 2 ^ (0 : ℕ) := by
    have heq : (T i - pi i a0) * P i = -((pi i a0 - T i) * P i) := by noncomm_ring
    simpa only [heq, norm_neg, pow_zero, div_one] using ha0app i
  let s0 : State 0 := ⟨a0, ha0, ha0err⟩
  have hstep (n : ℕ) (s : State n) : ∃ t : State (n + 1),
      ‖t.val - s.val‖ ≤ C / 2 / 2 ^ n := by
    let R : ∀ i, H i →L[ℂ] H i := fun i => T i - pi i s.val
    let B : ∀ i, H i →L[ℂ] H i := fun i => projectionResidual (R i) (P i)
    have hP (i : I) : IsSelfAdjoint (P i) := isSelfAdjoint_starProjection (E i)
    have hR (i : I) : IsSelfAdjoint (R i) := (hT i).sub (s.property.1.map (pi i))
    have hB (i : I) : IsSelfAdjoint (B i) := isSelfAdjoint_projectionResidual (hR i) (hP i)
    have hBP (i : I) : B i * P i = R i * P i :=
      projectionResidual_mul (E i).isIdempotentElem_starProjection
    have hBnorm (i : I) : ‖B i‖ ≤ C / 2 / 2 ^ n := by
      calc
        ‖B i‖ ≤ 3 * ‖R i * P i‖ :=
          norm_projectionResidual_le (hR i) (hP i) (E i).starProjection_norm_le
        _ ≤ 3 * (C / 6 / 2 ^ n) :=
          mul_le_mul_of_nonneg_left (s.property.2 i).le (by norm_num)
        _ = C / 2 / 2 ^ n := by ring
    obtain ⟨c, hc, hcnorm, hcapp⟩ :=
      exists_selfAdjoint_norm_le_forall_norm_sub_mul_starProjection_lt
        pi hirr hne E B hB (C / 2 / 2 ^ n) (by positivity) hBnorm
        (by positivity : 0 < C / 6 / 2 ^ (n + 1))
    have herror (i : I) : ‖(T i - pi i (s.val + c)) * P i‖ < C / 6 / 2 ^ (n + 1) := by
      have heq : (T i - pi i (s.val + c)) * P i = -((pi i c - B i) * P i) := by
        calc
          (T i - pi i (s.val + c)) * P i = (R i - pi i c) * P i := by
            simp only [R, map_add]
            noncomm_ring
          _ = B i * P i - pi i c * P i := by rw [sub_mul, ← hBP i]
          _ = -((pi i c - B i) * P i) := by noncomm_ring
      rw [heq, norm_neg]
      exact hcapp i
    exact ⟨⟨s.val + c, s.property.1.add hc, herror⟩, by simpa using hcnorm⟩
  let s : ∀ n : ℕ, State n := fun n =>
    Nat.rec s0 (fun n q => Classical.choose (hstep n q)) n
  let c : ℕ → A := fun n => (s (n + 1)).val - (s n).val
  have hs0norm : ‖(s 0).val‖ ≤ C := ha0norm
  have hcself (n : ℕ) : IsSelfAdjoint (c n) :=
    (s (n + 1)).property.1.sub (s n).property.1
  have hcnorm (n : ℕ) : ‖c n‖ ≤ C / 2 / 2 ^ n := by
    exact Classical.choose_spec (hstep n (s n))
  have hcsum : Summable c := (summable_geometric_two' C).of_norm_bounded hcnorm
  have hcnormsum : Summable (fun n => ‖c n‖) :=
    (summable_geometric_two' C).of_nonneg_of_le (fun n => norm_nonneg (c n)) hcnorm
  have hpartial (n : ℕ) : (s n).val = (s 0).val + ∑ k ∈ Finset.range n, c k := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        (s (n + 1)).val = (s n).val + c n := by dsimp [c]; abel
        _ = (s 0).val + (∑ k ∈ Finset.range n, c k) + c n := by rw [ih]
        _ = (s 0).val + ∑ k ∈ Finset.range (n + 1), c k := by
          rw [Finset.sum_range_succ]
          abel
  let a : A := (s 0).val + ∑' n, c n
  have hsumself : IsSelfAdjoint (∑' n, c n) := by
    rw [IsSelfAdjoint, tsum_star]
    exact tsum_congr (fun n => (hcself n).star_eq)
  have haself : IsSelfAdjoint a := (s 0).property.1.add hsumself
  have hanorm : ‖a‖ ≤ 2 * C := by
    calc
      ‖a‖ ≤ ‖(s 0).val‖ + ‖∑' n, c n‖ := norm_add_le _ _
      _ ≤ C + ∑' n, ‖c n‖ := add_le_add hs0norm (norm_tsum_le_tsum_norm hcnormsum)
      _ ≤ C + ∑' n : ℕ, C / 2 / 2 ^ n :=
        add_le_add le_rfl (Summable.tsum_le_tsum hcnorm hcnormsum (summable_geometric_two' C))
      _ = 2 * C := by rw [tsum_geometric_two']; ring
  have hstendsto : Tendsto (fun n => (s n).val) atTop (nhds a) := by
    have hconst : Tendsto (fun _ : ℕ => (s 0).val) atTop (nhds (s 0).val) := tendsto_const_nhds
    have hadd := hconst.add hcsum.hasSum.tendsto_sum_nat
    rw [show (fun n => (s n).val) =
        (fun n => (s 0).val + ∑ k ∈ Finset.range n, c k) by
      funext n
      exact hpartial n]
    exact hadd
  have hgeom : Tendsto (fun n : ℕ => C / 6 / 2 ^ n) atTop (nhds 0) := by
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have heq : (fun n : ℕ => C / 6 / 2 ^ n) = (fun n : ℕ => (C / 6) * (1 / 2 : ℝ) ^ n) := by
      funext n
      simp only [div_eq_mul_inv, one_mul, inv_pow]
    rw [heq]
    convert tendsto_const_nhds.mul hpow using 1
    simp
  refine ⟨a, haself, hanorm, fun i => ?_⟩
  have hpi : Tendsto (fun n => pi i (s n).val) atTop (nhds (pi i a)) :=
    ((map_continuous (pi i)).tendsto a).comp hstendsto
  have hlimit : Tendsto (fun n => (T i - pi i (s n).val) * P i) atTop
      (nhds ((T i - pi i a) * P i)) :=
    (tendsto_const_nhds.sub hpi).mul tendsto_const_nhds
  have hnormzero : Tendsto (fun n => ‖(T i - pi i (s n).val) * P i‖) atTop (nhds 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (s n).property.2 i |>.le) hgeom
  exact tendsto_nhds_unique hlimit (tendsto_zero_iff_norm_tendsto_zero.mpr hnormzero)

/-- The coarse exact simultaneous interpolant acts correctly on each whole
finite-dimensional subspace, not just on its chosen basis. -/
theorem exists_selfAdjoint_norm_le_two_mul_forall_eq_on
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * C ∧
      ∀ i, ∀ x : H i, x ∈ E i → pi i a x = T i x := by
  obtain ⟨a, ha, hanorm, hexact⟩ :=
    exists_selfAdjoint_norm_le_two_mul_forall_sub_mul_starProjection_eq_zero
      pi hirr hne E T hT C hC hTC
  refine ⟨a, ha, hanorm, fun i x hx => ?_⟩
  have h := congrArg (fun S : H i →L[ℂ] H i => S x) (hexact i)
  have hp : (E i).starProjection x = x := (E i).starProjection_eq_self_iff.mpr hx
  have hz : T i x - pi i a x = 0 := by
    simpa [ContinuousLinearMap.mul_apply, hp] using h
  exact (sub_eq_zero.mp hz).symm

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
