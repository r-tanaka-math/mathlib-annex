import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Normalization into the unit sphere

Package ambient normalization as a sphere element, with its retraction and
positive radial scaling laws. No nontriviality assumption is required.
-/

namespace MathlibAnnex.Sphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unit direction of a nonzero vector. -/
noncomputable def normalizeToSphere (x : E) (hx : x ≠ 0) :
    Metric.sphere (0 : E) 1 :=
  ⟨NormedSpace.normalize x, by
    simpa [dist_eq_norm] using NormedSpace.norm_normalize hx⟩

@[simp] theorem coe_normalizeToSphere (x : E) (hx : x ≠ 0) :
    (normalizeToSphere x hx : E) = NormedSpace.normalize x := rfl

/-- Normalization retracts the unit sphere. -/
@[simp] theorem normalizeToSphere_unit (u : Metric.sphere (0 : E) 1) :
    normalizeToSphere (u : E) (ne_zero_of_mem_unit_sphere u) = u := by
  apply Subtype.ext
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)

/-- A positive change of radius preserves the unit direction. -/
theorem normalizeToSphere_pos_smul (u : Metric.sphere (0 : E) 1)
    {r : ℝ} (hr : 0 < r) :
    normalizeToSphere (r • (u : E))
      (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)) = u := by
  apply Subtype.ext
  change NormedSpace.normalize (r • (u : E)) = (u : E)
  rw [NormedSpace.normalize_smul_of_pos hr]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)

end MathlibAnnex.Sphere
