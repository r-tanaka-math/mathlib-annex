/- Quantitative Hilbert models assembled through the general increment-locality
criterion. The coordinate-locality construction remains available separately.
No additional analytic hypothesis or instance fills the common data fields.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.CoordinateBridge
import BanachGeometry.LipschitzFreeSpace.HilbertLocality

noncomputable section
open scoped NNReal
namespace BanachGeometry.HilbertSums
open Nonlinear HilbertFreeSpace LipschitzFreeLocalization

/-- Complete continuity of the actual defect, now obtained via the general increment theorem. -/
theorem completelyContinuous_hilbertDefect_general (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    CompletelyContinuous (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize (hilbertDefect c hc hc')) := by
  let D : Base → GradedHilbert := hilbertDefect c hc hc'
  have hD := defect_lipschitz c hc.le (hilbertEquiv c hc hc')
    (fun z z' => (hilbertEquiv_bounds c hc hc' z z').2)
  have hD0 : D 0 = 0 := by simp [D, hilbertDefect, hilbertEquiv_zero]
  have hflat : LipschitzWith (⟨2 + 4 * c, by positivity⟩ : ℝ≥0) (fun z => flattenEquiv (D z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← flattenEquiv.map_sub, flattenEquiv.norm_map]
    simpa only [dist_eq_norm, D, hilbertDefect] using hD.dist_le_mul x y
  have hinc : IncrementLocality (fun z : Base => flattenEquiv (D z)) :=
    incrementLocality_of_coordinateLocalOrthogonality
    (fun z => flattenEquiv (D z)) (hilbertDefect_localOrthogonality c hc hc')
  have hcc := completelyContinuous_linearize_of_incrementLocality
    (fun z => flattenEquiv (D z)) hflat (by simp [hD0]) hinc
  apply completelyContinuous_of_isometry_comp flattenEquiv (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D)
  rw [← linearize_flatten D hD hD0]
  exact hcc

/-- The same concrete A,H,Q,d,h, with a proof through the general localization criterion. -/
def hilbertFreeSpaceData (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4) :
    QuantitativeHilbertData c freeBundle hilbertBundle where
  d := HilbertFreeSpace.d
  d_isometry := d_isometry
  d_zero := d_zero
  linearMap := BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize (hilbertDefect c hc hc')
  linearMap_completelyContinuous := completelyContinuous_hilbertDefect_general c hc hc'
  no_c0 := freeBanach_no_c0
  h := hilbertEquiv c hc hc'
  h_zero := hilbertEquiv_zero c hc hc'
  h_norm := norm_hilbertEquiv c hc hc'
  lower z z' := (hilbertEquiv_bounds c hc hc' z z').1
  upper z z' := (hilbertEquiv_bounds c hc hc' z z').2
  linearization z := BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize_point _
    (defect_lipschitz c hc.le (hilbertEquiv c hc hc') (fun z z' => (hilbertEquiv_bounds c hc hc' z z').2))
    (by simp [hilbertDefect, hilbertEquiv_zero]) z

/-- Quantitative Hilbert models for every 0 < c < 1/4, using the concrete
free-space and Hilbert bundles, the norm-preserving equivalence and the general
increment-locality criterion. Local execution evidence is in the external
qualification receipts; Annex, hosted and release status are recorded separately. -/
theorem exists_quantitativeHilbertData : HasQuantitativeHilbertModels := by
  intro c hc hc'
  exact ⟨freeBundle, hilbertBundle, ⟨hilbertFreeSpaceData c hc hc'⟩⟩

end BanachGeometry.HilbertSums
