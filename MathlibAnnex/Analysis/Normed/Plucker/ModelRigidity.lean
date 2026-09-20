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
  linearMap : (Fin (m + 1) → ℝ) →linearMap[ℝ] (Fin (m + 1) → ℝ)
  injective : Function.Injective linearMap
  surjective : Function.Surjective linearMap
  image_closedUnitBall : linearMap '' MX.closedUnitBall = MY.closedUnitBall
  seminorm_linearMap_eq : ∀ x, MY.p (linearMap x) = MX.p x

private theorem nonempty_coordinateLinearIsometry_of_all_body_eq {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (CoordinateLinearIsometryCertificate MX MY) := by
  let C := Classical.choice (PluckerRecovery.nonempty_limitCertificate_of_pluckerBodies_eq MX MY hBodies)
  have hball : C.linearMap '' MX.closedUnitBall = MY.closedUnitBall := C.image_unitBall_eq
  exact ⟨{
    linearMap := C.linearMap
    injective := C.injective
    surjective := C.surjective
    image_closedUnitBall := hball
    seminorm_linearMap_eq := fun x => SeminormBall.map_eq MX.p MY.p
      (fun _ h => MX.eq_zero_of_apply_eq_zero h)
      (fun _ h => MY.eq_zero_of_apply_eq_zero h) C.L.toLinearMap
      ⟨C.injective, C.surjective⟩ hball x }⟩
end PluckerRecovery.Internal

namespace EquivalentSeminorm
/-- Equality of all finite Plücker bodies gives an equivalence preserving the stored norms. -/
theorem nonempty_linearIsometryEquiv_of_pluckerBodies_eq {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (LinearIsometryEquiv MX MY) := by
  let C := Classical.choice (PluckerRecovery.Internal.nonempty_coordinateLinearIsometry_of_all_body_eq MX MY hBodies)
  let e : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    LinearEquiv.ofBijective C.L.toLinearMap ⟨C.injective, C.surjective⟩
  exact ⟨{ toLinearEquiv := e, map_p_eq := fun x => by simpa [e] using C.seminorm_linearMap_eq x }⟩

/-- Sphere isometry supplies the exact B3 body equality used by recovery. -/
theorem nonempty_linearIsometryEquiv_of_sphereIsometryEquiv {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1) :
    Nonempty (LinearIsometryEquiv MX MY) := by
  apply nonempty_linearIsometryEquiv_of_pluckerBodies_eq MX MY
  intro N
  exact PluckerBody.eq_of_sphereIsometry Δ
end EquivalentSeminorm
end MathlibAnnex
