import MathlibAnnex.Analysis.Normed.Plucker.LimitRecovery
import MathlibAnnex.Analysis.Normed.Plucker.BodyInvariance
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport

noncomputable section
set_option autoImplicit false
open Set
universe u v

namespace MathlibAnnex
namespace PluckerRecovery.Internal
/-- Private coordinate witness retaining bijectivity, ball image and exact norm equality. -/
private structure CoordinateLinearIsometryCertificate {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) where
  L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)
  injective : Function.Injective L
  surjective : Function.Surjective L
  unitBall_image : L '' MX.closedUnitBall = MY.closedUnitBall
  modelNorm_eq : ∀ x, MY.p (L x) = MX.p x

private theorem exists_coordinateLinearIsometry_of_all_body_eq {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (CoordinateLinearIsometryCertificate MX MY) := by
  let C := Classical.choice (PluckerRecovery.exists_limitCertificate_of_pluckerBodies_eq MX MY hBodies)
  have hball : C.L '' MX.closedUnitBall = MY.closedUnitBall := C.image_unitBall_eq
  exact ⟨{
    L := C.L
    injective := C.injective
    surjective := C.surjective
    unitBall_image := hball
    modelNorm_eq := fun x => SeminormBall.map_eq MX.p MY.p
      (fun _ h => MX.eq_zero_of_apply_eq_zero h)
      (fun _ h => MY.eq_zero_of_apply_eq_zero h) C.L.toLinearMap
      ⟨C.injective, C.surjective⟩ hball x }⟩
end PluckerRecovery.Internal

namespace EquivalentSeminorm
/-- Equality of all finite Plücker bodies gives an equivalence preserving the stored norms. -/
theorem exists_linearIsometryEquiv_of_pluckerBodies_eq {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (LinearIsometryEquiv MX MY) := by
  let C := Classical.choice (PluckerRecovery.Internal.exists_coordinateLinearIsometry_of_all_body_eq MX MY hBodies)
  let e : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    LinearEquiv.ofBijective C.L.toLinearMap ⟨C.injective, C.surjective⟩
  exact ⟨{ toLinearEquiv := e, map_p_eq := fun x => by simpa [e] using C.modelNorm_eq x }⟩

/-- Sphere isometry supplies the exact B3 body equality used by recovery. -/
theorem linearIsometryEquiv_of_sphereIsometryEquiv {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1) :
    Nonempty (LinearIsometryEquiv MX MY) := by
  apply exists_linearIsometryEquiv_of_pluckerBodies_eq MX MY
  intro N
  exact PluckerBody.eq_of_sphereIsometry Δ
end EquivalentSeminorm
end MathlibAnnex
