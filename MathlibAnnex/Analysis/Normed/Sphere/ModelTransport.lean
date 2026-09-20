import MathlibAnnex.Analysis.Normed.Plucker.ModelRigidity
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport
import MathlibAnnex.Analysis.Normed.Sphere.Dimension

noncomputable section
set_option autoImplicit false
open Set
universe u v

namespace MathlibAnnex.Sphere
/-- Transport the accepted model theorem through any common finite coordinate system. -/
theorem nonempty_linearIsometryEquiv_of_coordinate_model
    {m : ℕ} {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Δ : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1)
    (eX : (Fin (m + 1) → ℝ) ≃L[ℝ] X)
    (eY : (Fin (m + 1) → ℝ) ≃L[ℝ] Y) : Nonempty (X ≃ₗᵢ[ℝ] Y) := by
  let MX := EquivalentSeminorm.ofContinuousLinearEquiv eX
  let MY := EquivalentSeminorm.ofContinuousLinearEquiv eY
  let ΔM := EquivalentSeminorm.sphereIsometryEquiv eX eY Δ
  rcases EquivalentSeminorm.nonempty_linearIsometryEquiv_of_sphereIsometryEquiv MX MY ΔM with ⟨A⟩
  exact ⟨EquivalentSeminorm.transportLinearIsometryEquiv eX eY A⟩
end MathlibAnnex.Sphere
