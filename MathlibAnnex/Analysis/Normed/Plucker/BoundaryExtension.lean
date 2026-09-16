import MathlibAnnex.Analysis.Normed.Plucker.Average
import MathlibAnnex.Analysis.Normed.Sphere.Basic
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Boundary extensions with a derivative average in the Plücker body

Finite-coordinate McShane extension is performed in the norm of `Space M`.
The reference coordinates retain their original norm and Lebesgue measure.
The public existence theorem retains every field of the private witness.
-/

noncomputable section

open Set MeasureTheory
open MathlibAnnex.EquivalentSeminorm

namespace MathlibAnnex.Plucker

namespace Internal

private def modelBoundaryAmbient {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    (g : M.unitSphere → (Fin N → ℝ)) : Space M → (Fin N → ℝ) :=
  fun x => if hx : M.p (show Fin n → ℝ from x) = 1 then g ⟨_, hx⟩ else 0

private theorem modelBoundaryAmbient_lipschitzOn {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (g : M.unitSphere → (Fin N → ℝ))
    (hg : ∀ u v, ‖g u - g v‖ ≤ M.p ((u : Fin n → ℝ) - (v : Fin n → ℝ))) :
    LipschitzOnWith 1 (modelBoundaryAmbient M g) (Metric.sphere (0 : Space M) 1) := by
  refine LipschitzOnWith.mk_one ?_
  intro x hx y hy
  have hx' : M.p (show Fin n → ℝ from x) = 1 := mem_sphere_zero_iff_norm.mp hx
  have hy' : M.p (show Fin n → ℝ from y) = 1 := mem_sphere_zero_iff_norm.mp hy
  have hxy := hg ⟨(show Fin n → ℝ from x), hx'⟩ ⟨(show Fin n → ℝ from y), hy'⟩
  calc
    dist (modelBoundaryAmbient M g x) (modelBoundaryAmbient M g y) =
        ‖g ⟨(show Fin n → ℝ from x), hx'⟩ -
          g ⟨(show Fin n → ℝ from y), hy'⟩‖ := by
      simp [modelBoundaryAmbient, hx', hy', dist_eq_norm]
    _ ≤ M.p ((show Fin n → ℝ from x) - (show Fin n → ℝ from y)) := hxy
    _ = dist x y := (M.dist_space_eq x y).symm

private def modelMcShaneToCoord {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    (g : M.unitSphere → (Fin N → ℝ))
    (hg : ∀ u v, ‖g u - g v‖ ≤ M.p ((u : Fin n → ℝ) - (v : Fin n → ℝ))) :
    (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x => Classical.choose ((modelBoundaryAmbient_lipschitzOn M g hg).extend_pi)
    (show Space M from x)

private theorem modelMcShaneToCoord_spec {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (g : M.unitSphere → (Fin N → ℝ))
    (hg : ∀ u v, ‖g u - g v‖ ≤ M.p ((u : Fin n → ℝ) - (v : Fin n → ℝ))) :
    (∀ x y, ‖modelMcShaneToCoord M g hg x - modelMcShaneToCoord M g hg y‖ ≤
      M.p (x - y)) ∧ (∀ u : M.unitSphere, modelMcShaneToCoord M g hg u = g u) := by
  have hs := Classical.choose_spec ((modelBoundaryAmbient_lipschitzOn M g hg).extend_pi)
  constructor
  · intro x y
    have h := hs.1.dist_le_mul (show Space M from x) (show Space M from y)
    simpa only [modelMcShaneToCoord, NNReal.coe_one, one_mul, dist_eq_norm,
      norm_space_eq, toReference_sub_ofReference]
      using h
  · intro u
    have hu' : M.p u.val = 1 := u.property
    have hu : (show Space M from u.val) ∈ Metric.sphere (0 : Space M) 1 :=
      mem_sphere_zero_iff_norm.mpr u.property
    simpa [modelMcShaneToCoord, modelBoundaryAmbient, hu'] using (hs.2 hu).symm

private structure BoundaryExtensionData {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (g : M.unitSphere → (Fin N → ℝ)) where
  toFun : (Fin n → ℝ) → (Fin N → ℝ)
  modelLipschitz : ∀ x y, ‖toFun x - toFun y‖ ≤ M.p (x - y)
  onSphere : ∀ u : M.unitSphere, toFun (u : Fin n → ℝ) = g u
  derivative_contraction_ae :
    ∀ᵐ x ∂volume.restrict M.closedUnitBall, M.IsContraction (fderiv ℝ toFun x)
  derivativePlucker_integrable :
    IntegrableOn (derivativeGenerator M toFun) M.closedUnitBall volume
  average_mem : derivativeAverage M toFun ∈ PluckerBody.body M N

private def concreteBoundaryExtensionData {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (g : M.unitSphere → (Fin N → ℝ))
    (hg : ∀ u v, ‖g u - g v‖ ≤ M.p ((u : Fin n → ℝ) - (v : Fin n → ℝ))) :
    BoundaryExtensionData M g := by
  have h := modelMcShaneToCoord_spec M g hg
  have hc : ∀ᵐ x ∂volume.restrict M.closedUnitBall,
      M.IsContraction (fderiv ℝ (modelMcShaneToCoord M g hg) x) :=
    FDeriv.ae_norm_apply_le_seminorm_of_lipschitz M.p
      ⟨M.upper, M.upper_pos.le⟩ M.le_upper h.1 M.closedUnitBall
  have hi := derivativeGenerator_integrable_of_seminormLipschitz M h.1
  exact ⟨modelMcShaneToCoord M g hg, h.1, h.2, hc, hi,
    derivativeAverage_mem_body M hc hi⟩

end Internal

/-- Every seminorm-Lipschitz boundary map has an extension with its prescribed
trace, almost everywhere contractive derivative, integrable derivative
generator, and derivative average in the Plücker body. -/
theorem exists_extension_with_derivativeAverage_mem {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (g : M.unitSphere → (Fin N → ℝ))
    (hg : ∀ u v, ‖g u - g v‖ ≤ M.p ((u : Fin n → ℝ) - (v : Fin n → ℝ))) :
    ∃ f : (Fin n → ℝ) → (Fin N → ℝ),
      (∀ x y, ‖f x - f y‖ ≤ M.p (x - y)) ∧
      (∀ u : M.unitSphere, f u = g u) ∧
      (∀ᵐ x ∂volume.restrict M.closedUnitBall, M.IsContraction (fderiv ℝ f x)) ∧
      IntegrableOn (derivativeGenerator M f) M.closedUnitBall volume ∧
      derivativeAverage M f ∈ PluckerBody.body M N := by
  let d := Internal.concreteBoundaryExtensionData M g hg
  exact ⟨d.toFun, d.modelLipschitz, d.onSphere, d.derivative_contraction_ae,
    d.derivativePlucker_integrable, d.average_mem⟩

namespace Internal

private def coordinateBoundaryData {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) : MX.unitSphere → (Fin N → ℝ) :=
  fun u => A (show Fin (m + 1) → ℝ from
    (Δ ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩).val)

private theorem coordinateBoundaryData_modelLipschitz {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) (hA : MY.IsContraction A) :
    ∀ u v, ‖coordinateBoundaryData Δ A u - coordinateBoundaryData Δ A v‖ ≤
      MX.p ((u : Fin (m + 1) → ℝ) - (v : Fin (m + 1) → ℝ)) := by
  intro u v
  let u' : Metric.sphere (0 : Space MX) 1 :=
    ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩
  let v' : Metric.sphere (0 : Space MX) 1 :=
    ⟨(show Space MX from v.val), mem_sphere_zero_iff_norm.mpr v.property⟩
  have chord : MY.p ((show Fin (m + 1) → ℝ from (Δ u').val) -
      (show Fin (m + 1) → ℝ from (Δ v').val)) = MX.p (u.val - v.val) := by
    simpa only [Subtype.dist_eq, dist_space_eq] using Δ.isometry.dist_eq u' v'
  calc
    ‖coordinateBoundaryData Δ A u - coordinateBoundaryData Δ A v‖ =
        ‖A ((show Fin (m + 1) → ℝ from (Δ u').val) -
          (show Fin (m + 1) → ℝ from (Δ v').val))‖ := by
      simp [coordinateBoundaryData, u', v', map_sub]
    _ ≤ MY.p ((show Fin (m + 1) → ℝ from (Δ u').val) -
        (show Fin (m + 1) → ℝ from (Δ v').val)) := hA _
    _ = MX.p (u.val - v.val) := chord

private def boundaryExtensionData {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) (hA : MY.IsContraction A) :
    BoundaryExtensionData MX (coordinateBoundaryData Δ A) :=
  concreteBoundaryExtensionData MX (coordinateBoundaryData Δ A)
    (coordinateBoundaryData_modelLipschitz Δ A hA)

end Internal
end MathlibAnnex.Plucker
