import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation

/-!
# Finite-rank normalization of a represented self-adjoint element

This first step supplies a small self-adjoint additive correction, including
the off-diagonal block.  It does not yet assert a near-identity bilateral
factorization of the corrected positive contraction.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uH

theorem StarAlgHom.exists_small_selfAdjoint_correction
    {A : Type uA} [CStarAlgebra A]
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (a : A) (ha : IsSelfAdjoint a) :
    ∃ c : A, IsSelfAdjoint c ∧
      ‖c‖ ≤ 3 * ‖(1 - pi a) * E.starProjection‖ ∧
      ∀ x : H, x ∈ E → pi (a + c) x = x := by
  let P : H →L[ℂ] H := E.starProjection
  let R : H →L[ℂ] H := 1 - pi a
  have hR : IsSelfAdjoint R := by
    rw [IsSelfAdjoint]
    simp [R, ha.map pi |>.star_eq]
  have hP : IsSelfAdjoint P := isSelfAdjoint_starProjection E
  let S : H →L[ℂ] H := projectionResidual R P
  have hS : IsSelfAdjoint S := isSelfAdjoint_projectionResidual hR hP
  obtain ⟨c, hc, hcnorm, hcexact⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on pi hpi E S hS
  have hSnorm : ‖S‖ ≤ 3 * ‖R * P‖ :=
    norm_projectionResidual_le hR hP E.starProjection_norm_le
  refine ⟨c, hc, hcnorm.trans hSnorm, ?_⟩
  intro x hx
  have hPx : P x = x := E.starProjection_eq_self_iff.mpr hx
  have hRx : S x = R x := by
    have hmul := projectionResidual_mul E.isIdempotentElem_starProjection
      (R := R) (P := P)
    have happ := congrArg (fun T : H →L[ℂ] H => T x) hmul
    simpa [ContinuousLinearMap.mul_apply, hPx] using happ
  have hcRx : pi c x = R x := (hcexact x hx).trans hRx
  calc
    pi (a + c) x = pi a x + pi c x := by simp
    _ = pi a x + (1 - pi a) x := by rw [hcRx]
    _ = x := by simp

end MathlibAnnex.Analysis.CStarAlgebra
