import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Topology
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Transport to the norm of an equivalent seminorm

`Space M` is a separate carrier whose norm is `M.p`. The original carrier retains
its reference norm. Public transport equations use explicit carrier identities,
so their statements expose no private helper names.
-/

noncomputable section

namespace MathlibAnnex.EquivalentSeminorm

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A separate copy of the carrier, equipped below with the model norm. -/
def Space (_M : EquivalentSeminorm E) := E

variable (M : EquivalentSeminorm E)

instance : AddCommGroup (Space M) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (Space M) := inferInstanceAs (Module ℝ E)
instance : Norm (Space M) := ⟨fun x => M.p (show E from x)⟩

private theorem normedSpaceCore_space : NormedSpace.Core ℝ (Space M) where
  norm_nonneg x := apply_nonneg M.p (show E from x)
  norm_smul c x := by
    change M.p (c • (show E from x)) = ‖c‖ * M.p (show E from x)
    exact map_smul_eq_mul M.p c (show E from x)
  norm_triangle x y := map_add_le_add M.p (show E from x) (show E from y)
  norm_eq_zero_iff x := by
    change M.p (show E from x) = 0 ↔ (show E from x) = 0
    exact ⟨M.eq_zero_of_apply_eq_zero, fun h => by simp [h]⟩

instance : NormedAddCommGroup (Space M) := NormedAddCommGroup.ofCore (normedSpaceCore_space M)
instance : NormedSpace ℝ (Space M) := NormedSpace.ofCore (normedSpaceCore_space M)

private def ofReference (x : E) : Space M := x
private def toReference (x : Space M) : E := x

include M in
theorem toReference_ofReference (x : E) :
    (show E from (show Space M from x)) = x := rfl

theorem ofReference_toReference (x : Space M) :
    (show Space M from (show E from x)) = x := rfl

@[simp] theorem toReference_zero : (show E from (0 : Space M)) = 0 := rfl

@[simp] theorem toReference_sub (x y : Space M) :
    (show E from (x - y)) = (show E from x) - (show E from y) := rfl

@[simp] theorem toReference_sub_ofReference (x y : E) :
    (show E from ((show Space M from x) - (show Space M from y))) = x - y := rfl

@[simp] theorem norm_space_eq (x : Space M) : ‖x‖ = M.p (show E from x) := rfl

/-- Model distance is exactly the seminorm of the reference difference. -/
theorem dist_space_eq (x y : Space M) :
    dist x y = M.p ((show E from x) - (show E from y)) := by
  rw [dist_eq_norm]
  rfl

@[simp] theorem sphere_apply (u : Metric.sphere (0 : Space M) 1) :
    M.p (show E from u.val) = 1 :=
  mem_sphere_zero_iff_norm.mp u.property

/-- A linear equivalence preserving the two stored seminorms. -/
structure LinearIsometryEquiv (MX : EquivalentSeminorm E) (MY : EquivalentSeminorm F) where
  toLinearEquiv : E ≃ₗ[ℝ] F
  map_p_eq : ∀ x, MY.p (toLinearEquiv x) = MX.p x

/-- Pull the target norm back along a continuous linear equivalence.
The maxima with `1` keep both comparison constants positive in dimension zero. -/
def ofContinuousLinearEquiv (e : E ≃L[ℝ] X) : EquivalentSeminorm E where
  p := (normSeminorm ℝ X).comp e.toLinearMap
  lower := (max ‖(e.symm : X →L[ℝ] E)‖ 1)⁻¹
  upper := max ‖(e : E →L[ℝ] X)‖ 1
  lower_pos := inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  upper_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  lower_le := by
    intro x
    have hD : 0 < max ‖(e.symm : X →L[ℝ] E)‖ 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hbase : ‖x‖ ≤ ‖(e.symm : X →L[ℝ] E)‖ * ‖e x‖ := by
      simpa using ((e.symm : X →L[ℝ] E).le_opNorm (e x))
    have hmax : ‖x‖ ≤ max ‖(e.symm : X →L[ℝ] E)‖ 1 * ‖e x‖ :=
      hbase.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    calc
      (max ‖(e.symm : X →L[ℝ] E)‖ 1)⁻¹ * ‖x‖ ≤
          (max ‖(e.symm : X →L[ℝ] E)‖ 1)⁻¹ *
            (max ‖(e.symm : X →L[ℝ] E)‖ 1 * ‖e x‖) :=
        mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr hD.le)
      _ = ‖e x‖ := by rw [← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  le_upper := by
    intro x
    calc
      ‖e x‖ ≤ ‖(e : E →L[ℝ] X)‖ * ‖x‖ := (e : E →L[ℝ] X).le_opNorm x
      _ ≤ max ‖(e : E →L[ℝ] X)‖ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  continuous_p := by
    change Continuous (fun x : E => ‖e x‖)
    exact continuous_norm.comp e.continuous

namespace Internal

private def coordinateSeminorm (e : E ≃L[ℝ] X) : Seminorm ℝ E :=
  (normSeminorm ℝ X).comp e.toLinearMap

@[simp] private theorem coordinateSeminorm_apply (e : E ≃L[ℝ] X) (x : E) :
    coordinateSeminorm e x = ‖e x‖ := rfl

end Internal

@[simp] theorem ofContinuousLinearEquiv_p_apply (e : E ≃L[ℝ] X) (x : E) :
    (ofContinuousLinearEquiv e).p x = ‖e x‖ := Internal.coordinateSeminorm_apply e x

/-- Coordinate equivalence of the model sphere and the original target sphere. -/
def unitSphereEquiv (e : E ≃L[ℝ] X) :
    Metric.sphere (0 : Space (ofContinuousLinearEquiv e)) 1 ≃
      Metric.sphere (0 : X) 1 where
  toFun u := ⟨e (show E from u.val), by
    apply mem_sphere_zero_iff_norm.mpr
    exact sphere_apply (ofContinuousLinearEquiv e) u⟩
  invFun u := ⟨(show Space (ofContinuousLinearEquiv e) from e.symm u.val), by
    apply mem_sphere_zero_iff_norm.mpr
    change ‖e (e.symm u.val)‖ = 1
    rw [e.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp u.property⟩
  left_inv u := by apply Subtype.ext; exact e.symm_apply_apply (show E from u.val)
  right_inv u := by apply Subtype.ext; exact e.apply_symm_apply u.val

/-- Transport a sphere isometry to the two model normed spaces. -/
def sphereIsometryEquiv (eX : E ≃L[ℝ] X) (eY : F ≃L[ℝ] Y)
    (Δ : Metric.sphere (0 : X) 1 ≃ᵢ Metric.sphere (0 : Y) 1) :
    Metric.sphere (0 : Space (ofContinuousLinearEquiv eX)) 1 ≃ᵢ
      Metric.sphere (0 : Space (ofContinuousLinearEquiv eY)) 1 := by
  let cX := unitSphereEquiv eX
  let cY := unitSphereEquiv eY
  refine { toEquiv := cX.trans (Δ.toEquiv.trans cY.symm), isometry_toFun := ?_ }
  apply isometry_iff_dist_eq.mpr
  intro u v
  change dist (cY.symm (Δ (cX u))) (cY.symm (Δ (cX v))) = dist u v
  have hx : ∀ a b, dist (cX a) (cX b) = dist a b := by
    intro a b
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_space_eq]
    change ‖eX (show E from a.val) - eX (show E from b.val)‖ =
      ‖eX ((show E from a.val) - (show E from b.val))‖
    rw [map_sub]
  have hy : ∀ a b, dist (cY.symm a) (cY.symm b) = dist a b := by
    intro a b
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_space_eq, dist_eq_norm]
    change ‖eY (eY.symm a.val - eY.symm b.val)‖ = ‖a.val - b.val‖
    rw [map_sub, eY.apply_symm_apply, eY.apply_symm_apply]
  rw [hy, Δ.isometry.dist_eq, hx]

/-- Transport a model norm preserving linear equivalence to the original spaces. -/
def transportLinearIsometryEquiv (eX : E ≃L[ℝ] X) (eY : F ≃L[ℝ] Y)
    (A : LinearIsometryEquiv (ofContinuousLinearEquiv eX) (ofContinuousLinearEquiv eY)) :
    X ≃ₗᵢ[ℝ] Y := by
  let L : X ≃ₗ[ℝ] Y := eX.toLinearEquiv.symm.trans (A.toLinearEquiv.trans eY.toLinearEquiv)
  exact {
    toLinearEquiv := L
    norm_map' := by
      intro x
      have h := A.map_p_eq (eX.symm x)
      simpa [L] using h }

end MathlibAnnex.EquivalentSeminorm
