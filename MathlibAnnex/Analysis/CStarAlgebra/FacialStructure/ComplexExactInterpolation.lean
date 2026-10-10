/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousClipping

/-!
# Complex exact interpolation on finite-dimensional ranges

An arbitrary bounded complex operator is reconstructed from two self-adjoint
interpolants on a finite-dimensional range.  This reusable theorem is kept
outside the compact-intersection module; no compactness assumption is used.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe v
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Interpolation

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (hclosed : IsClosed (S : Set (H →L[ℂ] H)))

include hclosed in
/-- On the range of a finite-rank operator, an arbitrary bounded operator can
be matched by an element of an irreducible norm-closed operator algebra, with
norm at most twice the original operator norm. -/
theorem exists_norm_le_two_mul_eq_on_range
    (hS : letI : NonUnitalCStarAlgebra S :=
        NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
      NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (F b : H →L[ℂ] H) [FiniteDimensional ℂ (LinearMap.range F.toLinearMap)] :
    ∃ s : S, ‖s‖ ≤ 2 * ‖b‖ ∧
      ∀ x : H, x ∈ LinearMap.range F.toLinearMap → s.val x = b x := by
  letI : NonUnitalCStarAlgebra S :=
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S (h_closed := hclosed)
  let R : H →L[ℂ] H := b + star b
  let I : H →L[ℂ] H := Complex.I • (b - star b)
  have hR : IsSelfAdjoint R := by
    change star (b + star b) = b + star b
    rw [star_add, star_star, add_comm]
  have hI : IsSelfAdjoint I := by
    change star (Complex.I • (b - star b)) = Complex.I • (b - star b)
    rw [star_smul, show star Complex.I = -Complex.I by simp, star_sub, star_star,
      neg_smul, smul_sub, smul_sub]
    abel
  have hRnorm : ‖R‖ ≤ 2 * ‖b‖ := by
    calc
      ‖R‖ = ‖b + star b‖ := rfl
      _ ≤ ‖b‖ + ‖star b‖ := norm_add_le _ _
      _ = 2 * ‖b‖ := by rw [norm_star]; ring
  have hInorm : ‖I‖ ≤ 2 * ‖b‖ := by
    calc
      ‖I‖ = ‖b - star b‖ := by simp [I, norm_smul]
      _ ≤ ‖b‖ + ‖star b‖ := norm_sub_le _ _
      _ = 2 * ‖b‖ := by rw [norm_star]; ring
  obtain ⟨r, _hrself, hrnorm, hrange⟩ :=
    NonUnitalCStarRepresentation.exists_selfAdjoint_norm_le_forall_eq_on
      (I := Unit) (H := fun _ => H)
      (fun _ => NonUnitalStarSubalgebraClass.subtype S) (fun _ => hS)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ => LinearMap.range F.toLinearMap) (fun _ => R) (fun _ => hR)
      (2 * ‖b‖) (by positivity) (fun _ => hRnorm)
  obtain ⟨t, _htself, htnorm, htrange⟩ :=
    NonUnitalCStarRepresentation.exists_selfAdjoint_norm_le_forall_eq_on
      (I := Unit) (H := fun _ => H)
      (fun _ => NonUnitalStarSubalgebraClass.subtype S) (fun _ => hS)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ => LinearMap.range F.toLinearMap) (fun _ => I) (fun _ => hI)
      (2 * ‖b‖) (by positivity) (fun _ => hInorm)
  let s : S := (1 / 2 : ℂ) • r + (-Complex.I / 2) • t
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hIhalf : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_I]
    norm_num
  have hsnorm : ‖s‖ ≤ 2 * ‖b‖ := by
    calc
      ‖s‖ ≤ ‖(1 / 2 : ℂ) • r‖ + ‖(-Complex.I / 2) • t‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖r‖ + (1 / 2 : ℝ) * ‖t‖ := by
        rw [norm_smul, norm_smul, hhalf, hIhalf]
      _ ≤ (1 / 2 : ℝ) * (2 * ‖b‖) + (1 / 2 : ℝ) * (2 * ‖b‖) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hrnorm (by norm_num))
          (mul_le_mul_of_nonneg_left htnorm (by norm_num))
      _ = 2 * ‖b‖ := by ring
  refine ⟨s, hsnorm, ?_⟩
  intro x hx
  have hrx : r.val x = R x := by
    simpa only [NonUnitalStarSubalgebraClass.subtype_apply] using hrange () x hx
  have htx : t.val x = I x := by
    simpa only [NonUnitalStarSubalgebraClass.subtype_apply] using htrange () x hx
  have hc : (-Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
    calc
      (-Complex.I / 2) * Complex.I = -(Complex.I * Complex.I) / 2 := by ring
      _ = (1 / 2 : ℂ) := by rw [← pow_two, Complex.I_sq]; norm_num
  change ((1 / 2 : ℂ) • r.val + (-Complex.I / 2) • t.val) x = b x
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, hrx, htx]
  change (1 / 2 : ℂ) • ((b + star b) x) +
      (-Complex.I / 2) • ((Complex.I • (b - star b)) x) = b x
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_smul, hc, ← smul_add]
  have hsum : (b x + (star b) x) + (b x - (star b) x) = (2 : ℂ) • b x := by
    rw [two_smul]
    abel
  rw [hsum, smul_smul]
  norm_num

end Interpolation

end MathlibAnnex.Analysis.CStarAlgebra
