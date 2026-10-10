/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.ExtremeState

/-!
# Uniqueness of a positive unitary translate

This proves the uniqueness part of the extreme-functional polar theorem.
Positivity of a translate implies purity by extremality; the attained positive
contraction from the existing pure-state theorem fixes the GNS vector of any
second positive translate. The two translated functionals then agree on all
of the original algebra. The translating unitaries themselves need not agree.
Existence of a positive translate is not asserted.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

private theorem eq_of_norm_le_one_of_inner_eq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) (hxy : inner ℂ x y = 1) :
    y = x := by
  have hsq := norm_sub_sq (𝕜 := ℂ) x y
  rw [hx, hxy] at hsq
  have hz : ‖x - y‖ = 0 := by
    norm_num at hsq
    nlinarith [norm_nonneg (x - y), norm_nonneg y]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- Equality in the norm contraction for a positive contraction fixes the vector. -/
private theorem apply_eq_self_of_nonneg_of_norm_apply_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (hTnorm : ‖T‖ ≤ 1) (x : H)
    (hTx : ‖T x‖ = ‖x‖) : T x = x := by
  have hsqle : T * T ≤ T := mul_self_le_self_of_nonneg_of_norm_le_one T hT hTnorm
  have hpos : 0 ≤ T - T * T := sub_nonneg.mpr hsqle
  have hadj : ContinuousLinearMap.adjoint T = T := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hT.isSelfAdjoint.star_eq
  have hgram : inner ℂ x (T (T x)) = inner ℂ (T x) (T x) := by
    simpa only [hadj] using ContinuousLinearMap.adjoint_inner_right T x (T x)
  have hbound := (RCLike.nonneg_iff.mp (hpos.inner_nonneg_right x)).1
  simp only [sub_zero, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at hbound
  change 0 ≤ (inner ℂ x (T x - T (T x))).re at hbound
  have hself : (inner ℂ (T x) (T x)).re = ‖T x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
  rw [inner_sub_right, hgram, Complex.sub_re, hself] at hbound
  have hnorm := norm_sub_sq (𝕜 := ℂ) x (T x)
  rw [hTx] at hnorm hbound
  change ‖x - T x‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x (T x)).re + ‖x‖ ^ 2 at hnorm
  have hz : ‖x - T x‖ = 0 := by
    nlinarith [norm_nonneg (x - T x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

/-- Two positive unitary translates of an extreme dual unit functional are
identical. This is uniqueness of the state, not uniqueness of the unitary. -/
theorem unitaryTranslate_eq_of_nonneg_of_mem_extremePoints_dual_closedBall
    {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ)
    (u v : unitary (Unitization ℂ A))
    (hu : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate u rho a)
    (hv : ∀ a : A, 0 ≤ a → 0 ≤ unitaryTranslate v rho a) :
    unitaryTranslate u rho = unitaryTranslate v rho := by
  let phi := unitaryTranslate u rho
  let psi := unitaryTranslate v rho
  have hphiPure : IsPureNonUnitalState A phi := isPureNonUnitalState_unitaryTranslate u hrho hu
  have hpsiPure : IsPureNonUnitalState A psi := isPureNonUnitalState_unitaryTranslate v hrho hv
  have hpsi : psi ∈ nonUnitalStateSpace A := hpsiPure.1
  obtain ⟨e, he, hphie, henorm⟩ :=
    exists_nonneg_apply_eq_one_norm_eq_one_of_isPureNonUnitalState phi hphiPure
  let w : unitary (Unitization ℂ A) := star v * u
  have htranslate : unitaryTranslate w psi = phi := by
    dsimp only [psi, phi, w]
    rw [← unitaryTranslate_mul, ← mul_assoc, Unitary.mul_star_self, one_mul]
  let Psi : StrongDual ℂ (Unitization ℂ A) := unitizationExtension psi
  have hPsi : Psi ∈ stateSpace (Unitization ℂ A) := unitizationExtension_mem_stateSpace psi hpsi
  let f := positiveLinearMapOfMemStateSpace Psi hPsi
  let pi := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector Psi hPsi
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector Psi hPsi
  have recover (z : Unitization ℂ A) : inner ℂ xi (pi z xi) = Psi z :=
    inner_gnsStarAlgHom_stateGNSVector Psi hPsi z
  have hphi (a : A) : inner ℂ xi (pi ((w : Unitization ℂ A) * (a : Unitization ℂ A)) xi) = phi a := by
    rw [recover, ← inr_unitizationLeftMul]
    change unitizationExtension psi (Unitization.inr
      (unitizationLeftMul (w : Unitization ℂ A) a)) = phi a
    rw [unitizationExtension_inr]
    exact congrArg (fun q : StrongDual ℂ A => q a) htranslate
  let T := pi (e : Unitization ℂ A)
  let W := pi (w : Unitization ℂ A)
  have hT : 0 ≤ T := by
    simpa only [map_zero] using
      (OrderHomClass.mono pi (Unitization.inr_nonneg_iff.mpr he))
  have hTnorm : ‖T‖ ≤ 1 := by
    calc
      ‖T‖ ≤ ‖(e : Unitization ℂ A)‖ := NonUnitalStarAlgHom.norm_apply_le pi _
      _ = 1 := by rw [Unitization.norm_inr, henorm]
  have hWnorm : ‖W‖ ≤ 1 := by
    calc
      ‖W‖ ≤ ‖(w : Unitization ℂ A)‖ := NonUnitalStarAlgHom.norm_apply_le pi _
      _ = 1 := CStarRing.norm_coe_unitary w
  have hTxnorm : ‖T xi‖ ≤ 1 := by
    calc
      ‖T xi‖ ≤ ‖T‖ * ‖xi‖ := T.le_opNorm xi
      _ ≤ 1 := by rw [hxi, mul_one]; exact hTnorm
  have hWTxnorm : ‖W (T xi)‖ ≤ 1 := by
    calc
      ‖W (T xi)‖ ≤ ‖W‖ * ‖T xi‖ := W.le_opNorm _
      _ ≤ 1 * 1 := mul_le_mul hWnorm hTxnorm (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hWTxinner : inner ℂ xi (W (T xi)) = 1 := by
    have h := (hphi e).trans hphie
    rw [map_mul] at h
    exact h
  have hWTx : W (T xi) = xi :=
    eq_of_norm_le_one_of_inner_eq_one hxi hWTxnorm hWTxinner
  have hTxnormeq : ‖T xi‖ = ‖xi‖ := by
    apply le_antisymm (by simpa only [hxi] using hTxnorm)
    calc
      ‖xi‖ = ‖W (T xi)‖ := congrArg norm hWTx.symm
      _ ≤ ‖W‖ * ‖T xi‖ := W.le_opNorm _
      _ ≤ 1 * ‖T xi‖ := mul_le_mul_of_nonneg_right hWnorm (norm_nonneg _)
      _ = ‖T xi‖ := one_mul _
  have hTx : T xi = xi := apply_eq_self_of_nonneg_of_norm_apply_eq T hT hTnorm xi hTxnormeq
  have hWxi : W xi = xi := by simpa only [hTx] using hWTx
  have hstarWxi : ContinuousLinearMap.adjoint W xi = xi := by
    have hprod : ContinuousLinearMap.adjoint W * W = 1 := by
      change ContinuousLinearMap.adjoint (pi (w : Unitization ℂ A)) * pi (w : Unitization ℂ A) = 1
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul,
        Unitary.coe_star_mul_self, map_one]
    have h := congrArg (fun R : f.GNS →L[ℂ] f.GNS => R xi) hprod
    change ContinuousLinearMap.adjoint W (W xi) = xi at h
    simpa only [hWxi] using h
  apply ContinuousLinearMap.ext
  intro a
  calc
    phi a = inner ℂ xi (W (pi (a : Unitization ℂ A) xi)) := by
      rw [← hphi a, map_mul]
      rfl
    _ = inner ℂ (ContinuousLinearMap.adjoint W xi) (pi (a : Unitization ℂ A) xi) :=
      (ContinuousLinearMap.adjoint_inner_left W (pi (a : Unitization ℂ A) xi) xi).symm
    _ = inner ℂ xi (pi (a : Unitization ℂ A) xi) := by rw [hstarWxi]
    _ = psi a := by rw [recover]; exact unitizationExtension_inr psi a

end MathlibAnnex.Analysis.CStarAlgebra
