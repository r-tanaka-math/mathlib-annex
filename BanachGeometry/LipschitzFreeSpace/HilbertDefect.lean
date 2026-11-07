/- Concrete free-space, no-c₀ and specialized complete-continuity bridge using the
preserved generic port API. The local data-construction helpers take defect
local orthogonality explicitly; HilbertLocality proves it for the constructed
defect. The general increment theorem is supplied by Localization/GeneralCriterion.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Graded.CoordinateIsometry
import BanachGeometry.HilbertSums.Nonlinear.DistanceBounds
import BanachGeometry.LipschitzFreeSpace.UniversalProperties
import BanachGeometry.LipschitzFreeGeometry.CompactReduction
import BanachGeometry.LipschitzFreeGeometry.CompactHilbertWSC

noncomputable section
open scoped Topology NNReal
namespace BanachGeometry.HilbertFreeSpace
open BanachGeometry.HilbertSums BanachGeometry.HilbertSums.Nonlinear

abbrev Base := HilbertPair GradedHilbert
abbrev FreeBanach := BanachGeometry.LipschitzFreeGeometry.FreeSpace.Space Base

instance freeBanach_nontrivial : Nontrivial FreeBanach := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Base
  exact ⟨⟨BanachGeometry.LipschitzFreeGeometry.FreeSpace.point x, BanachGeometry.LipschitzFreeGeometry.FreeSpace.point y, fun h => hxy (BanachGeometry.LipschitzFreeGeometry.FreeSpace.isometry_point.injective h)⟩⟩

def freeBundle : SeparableRealBanach where
  Carrier := FreeBanach
  normedAddCommGroup := inferInstance
  normedSpace := inferInstance
  completeSpace := inferInstance
  separableSpace := inferInstance
  nontrivial := inferInstance

/-- Actual isometric pointed inclusion into the Lipschitz-free space. -/
def d : Base → FreeBanach := BanachGeometry.LipschitzFreeGeometry.FreeSpace.point

theorem d_isometry : Isometry d := BanachGeometry.LipschitzFreeGeometry.FreeSpace.isometry_point
@[simp] theorem d_zero : d 0 = 0 := BanachGeometry.LipschitzFreeGeometry.FreeSpace.point_zero

/-- WSC of the free space over the real Hilbert Base excludes an actual linear c0 copy. -/
theorem freeBanach_no_c0 : ¬ ContainsLinearCopy ScalarC0 FreeBanach := by
  exact LipschitzFreeProperties.hilbert_free_no_c0 (H := Base)

/-- Predicate translation, not a new mathematical assumption. -/
theorem weakNull_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℕ → E) :
    BanachGeometry.WeakNull u ↔ BanachGeometry.LipschitzFreeGeometry.WeakSequences.WeakNull u := Iff.rfl

theorem completelyContinuous_iff {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (T : E →L[ℝ] V) :
    BanachGeometry.CompletelyContinuous T ↔ BanachGeometry.LipschitzFreeGeometry.WeakSequences.CompletelyContinuous T := Iff.rfl

/-- Transfer complete continuity through an actual isometric equivalence of target spaces. -/
theorem completelyContinuous_of_isometry_comp
    {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (T : E →L[ℝ] V)
    (hT : BanachGeometry.CompletelyContinuous (e.toContinuousLinearEquiv.toContinuousLinearMap.comp T)) :
    BanachGeometry.CompletelyContinuous T := by
  intro u hu
  have ht := e.symm.continuous.tendsto 0 |>.comp (hT u hu)
  change Filter.Tendsto (fun n => e.symm (e (T (u n)))) Filter.atTop (𝓝 (e.symm 0)) at ht
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.symm_apply_apply,
    map_zero] using ht

/-- Universal-property compatibility of the actual linearization and flattening. -/
theorem linearize_flatten (D : Base → GradedHilbert) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hD0 : D 0 = 0) :
    BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize (fun x => flattenEquiv (D x)) =
      flattenEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D) := by
  have hflat : LipschitzWith L (fun x => flattenEquiv (D x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← flattenEquiv.map_sub, flattenEquiv.norm_map]
    simpa only [dist_eq_norm] using hD.dist_le_mul x y
  apply BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize_unique (fun x => flattenEquiv (D x)) hflat (by simp [hD0])
  intro x
  change flattenEquiv ((BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D)
    (BanachGeometry.LipschitzFreeGeometry.FreeSpace.point x)) = flattenEquiv (D x)
  rw [BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize_point D hD hD0]

/-- The main-sufficient coordinate specialization, using compact reduction of complete Base.
The coordinate LocalOrthogonality premise is strictly more specialized than general 8.1. -/
theorem defect_linearize_completelyContinuous (D : Base → GradedHilbert) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : BanachGeometry.LipschitzFreeGeometry.CoordinateLocality.LocalOrthogonality (fun x => flattenEquiv (D x))) :
    BanachGeometry.CompletelyContinuous (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D) := by
  have hflat : LipschitzWith L (fun x => flattenEquiv (D x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← flattenEquiv.map_sub, flattenEquiv.norm_map]
    simpa only [dist_eq_norm] using hD.dist_le_mul x y
  have hcc := BanachGeometry.LipschitzFreeGeometry.LocalizedLinearization.completely_continuous_of_compact_reduction
    (BanachGeometry.LipschitzFreeGeometry.FreeSpace.hasCompactReduction (M := Base)) (fun x => flattenEquiv (D x)) hflat
    (by simp [hD0]) hloc
  apply completelyContinuous_of_isometry_comp flattenEquiv (BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize D)
  rw [← linearize_flatten D hD hD0]
  exact hcc

/-- An arbitrary pointed h satisfying the contract bounds yields a Lipschitz defect. -/
theorem defect_lipschitz (c : ℝ) (hc : 0 ≤ c) (h : Base ≃ GradedHilbert)
    (hupper : ∀ z z', ‖h z - h z'‖ ≤ (1 + 4 * c) * ‖z - z'‖) :
    LipschitzWith (⟨2 + 4 * c, by positivity⟩ : ℝ≥0)
      (fun z => h z - (WithLp.ofLp z).1) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simp only [dist_eq_norm]
  change ‖(h z - (WithLp.ofLp z).1) - (h z' - (WithLp.ofLp z').1)‖ ≤
    (2 + 4 * c) * ‖z - z'‖
  have hp : ‖(WithLp.ofLp z).1 - (WithLp.ofLp z').1‖ ≤ ‖z - z'‖ := by
    simpa using (WithLp.norm_fst_le GradedHilbert (z - z'))
  have he : (h z - (WithLp.ofLp z).1) - (h z' - (WithLp.ofLp z').1) =
      (h z - h z') - ((WithLp.ofLp z).1 - (WithLp.ofLp z').1) := by module
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [hupper z z'])

/-- QuantitativeHilbertData from a supplied equivalence h with the stated
zero, norm and distance bounds, and explicit coordinate locality hloc.
For the concrete hilbertEquiv, HilbertLocality proves local orthogonality;
AlmostIsometric.HilbertFreeSpaceData assembles the same bundles using the
general increment-locality criterion. This local definition retains hloc. -/
def hilbertFreeSpaceDataOfLocality (c : ℝ) (hc : 0 < c) (h : Base ≃ GradedHilbert)
    (hzero : h 0 = 0) (hnorm : ∀ z, ‖h z‖ = ‖z‖)
    (hlower : ∀ z z', (1 - 4 * c) * ‖z - z'‖ ≤ ‖h z - h z'‖)
    (hupper : ∀ z z', ‖h z - h z'‖ ≤ (1 + 4 * c) * ‖z - z'‖)
    (hloc : BanachGeometry.LipschitzFreeGeometry.CoordinateLocality.LocalOrthogonality
      (fun z => flattenEquiv (h z - (WithLp.ofLp z).1))) :
    QuantitativeHilbertData c freeBundle hilbertBundle where
  d := d
  d_isometry := d_isometry
  d_zero := d_zero
  linearMap := BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize (fun z => h z - (WithLp.ofLp z).1)
  linearMap_completelyContinuous := defect_linearize_completelyContinuous _
    (defect_lipschitz c hc.le h hupper) (by simp [hzero]) hloc
  no_c0 := freeBanach_no_c0
  h := h
  h_zero := hzero
  h_norm := hnorm
  lower := hlower
  upper := hupper
  linearization z := BanachGeometry.LipschitzFreeGeometry.FreeSpace.linearize_point _ (defect_lipschitz c hc.le h hupper)
    (by simp [hzero]) z

/-- Use the concrete hEquiv built from the explicit comparison budget
hbudget, retaining locality hloc for its flattened defect. Equivalence proves
the comparison budget and HilbertLocality proves locality for the concrete
Hilbert equivalence; no such hypotheses are dropped for an arbitrary map. -/
def hilbertFreeSpaceDataOfBudgetAndLocality (c : ℝ) (hc : 0 < c) (hc' : c < 1 / 4)
    (hbudget : ComparisonBudget c hc)
    (hloc : BanachGeometry.LipschitzFreeGeometry.CoordinateLocality.LocalOrthogonality (fun z =>
      flattenEquiv (hEquiv c hc (by linarith) hbudget z - (WithLp.ofLp z).1))) :
    QuantitativeHilbertData c freeBundle hilbertBundle :=
  hilbertFreeSpaceDataOfLocality c hc (hEquiv c hc (by linarith) hbudget)
    (hEquiv_zero _ _ _ _) (norm_hEquiv _ _ _ _)
    (fun z z' => (hEquiv_distance_bounds c hc hc' hbudget z z').1)
    (fun z z' => (hEquiv_distance_bounds c hc hc' hbudget z z').2) hloc

/-- Explicit conditional supply, whose premise is not asserted or registered as an instance. -/
theorem quantitativeHilbertData_of_budget_and_locality
    (hbudget : ∀ c (hc : 0 < c), c < 1 / 4 → ComparisonBudget c hc)
    (hloc : ∀ c (hc : 0 < c) (hc' : c < 1 / 4),
      BanachGeometry.LipschitzFreeGeometry.CoordinateLocality.LocalOrthogonality (fun z => flattenEquiv
        (hEquiv c hc (by linarith) (hbudget c hc hc') z - (WithLp.ofLp z).1))) :
    HasQuantitativeHilbertModels := by
  intro c hc hc'
  exact ⟨freeBundle, hilbertBundle, ⟨hilbertFreeSpaceDataOfBudgetAndLocality c hc hc' (hbudget c hc hc')
    (hloc c hc hc')⟩⟩

end BanachGeometry.HilbertFreeSpace
