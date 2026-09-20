import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedCornerStates
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.NormalStateDomination
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Bounded strong-star convergence in the actual represented corner

The controlling functionals below are constructed from source predual tests
and the actual section. They are not arbitrary B(H) functionals declared
normal. Both square orientations, one index/filter, and an explicit uniform
operator bound are retained. The square WOT limit itself is proved directly
from inner products. C03 controller proof-source candidate, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarBidual MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarBilinear MathlibAnnex.Analysis.CStarAlgebra
universe u v t
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Strong convergence to zero implies WOT convergence of X*X to zero.
The product limit is not obtained by an invalid joint WOT-continuity claim. -/
theorem tendsto_star_square_wot_zero {ι : Type t} (l : Filter ι)
    (X : ι → H →L[ℂ] H)
    (hX : ∀ xi : H, Tendsto (fun i => X i xi) l (𝓝 0)) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (star (X i) * X i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (0 : H →L[ℂ] H))) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
  intro xi eta
  have h : Tendsto (fun i => ⟪X i eta, X i xi⟫_ℂ) l
      (𝓝 (⟪(0 : H), (0 : H)⟫_ℂ)) := (hX eta).inner (hX xi)
  simpa only [ContinuousLinearMapWOT.ofCLM_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.zero_apply, inner_zero_right, inner_zero_left] using h

/-- The reverse square uses the adjoint convergence, not the forward one. -/
theorem tendsto_reverse_square_wot_zero {ι : Type t} (l : Filter ι)
    (X : ι → H →L[ℂ] H)
    (hXs : ∀ xi : H, Tendsto (fun i => star (X i) xi) l (𝓝 0)) :
    Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (X i * star (X i))) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM (0 : H →L[ℂ] H))) := by
  simpa only [star_star] using
    tendsto_star_square_wot_zero l (fun i => star (X i)) hXs

variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- Any source predual test, after the actual section, has vanishing
strong-star gauge on a bounded strongly-star-null net. -/
theorem tendsto_cornerGauge_zero {ι : Type t} (l : Filter ι)
    (X : ι → H →L[ℂ] H)
    (hX : ∀ xi : H, Tendsto (fun i => X i xi) l (𝓝 0))
    (hXs : ∀ xi : H, Tendsto (fun i => star (X i) xi) l (𝓝 0))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖X i‖ ≤ r) (phi : StrongDual ℂ A) :
    Tendsto (fun i => strongStarGauge (cornerFunctional pi hpi phi) (X i)) l (𝓝 0) := by
  have hb : ∀ᶠ i in l,
      ‖star (X i) * X i‖ ≤ |r| ^ 2 ∧ ‖X i * star (X i)‖ ≤ |r| ^ 2 := by
    filter_upwards [hr] with i hi
    have hi' : ‖X i‖ ≤ |r| := hi.trans (le_abs_self r)
    constructor
    · calc
        ‖star (X i) * X i‖ ≤ ‖star (X i)‖ * ‖X i‖ := norm_mul_le _ _
        _ = ‖X i‖ * ‖X i‖ := by rw [norm_star]
        _ ≤ |r| * |r| := mul_le_mul hi' hi' (norm_nonneg _) (abs_nonneg _)
        _ = |r| ^ 2 := (pow_two _).symm
    · calc
        ‖X i * star (X i)‖ ≤ ‖X i‖ * ‖star (X i)‖ := norm_mul_le _ _
        _ = ‖X i‖ * ‖X i‖ := by rw [norm_star]
        _ ≤ |r| * |r| := mul_le_mul hi' hi' (norm_nonneg _) (abs_nonneg _)
        _ = |r| ^ 2 := (pow_two _).symm
  have h1 := tendsto_cornerFunctional pi hpi l (fun i => star (X i) * X i) 0
    (tendsto_star_square_wot_zero l X hX) (|r| ^ 2) (hb.mono fun _ h => h.1) phi
  have h2 := tendsto_cornerFunctional pi hpi l (fun i => X i * star (X i)) 0
    (tendsto_reverse_square_wot_zero l X hXs) (|r| ^ 2) (hb.mono fun _ h => h.2) phi
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp (h1.norm.add h2.norm)
  simpa only [Function.comp_def, strongStarGauge, map_zero, norm_zero, zero_add,
    Real.sqrt_zero] using h

/-- A translated bounded strong-star-convergent net. The same T(i)-U is used
in both squares; no test-dependent approximant is selected. -/
theorem tendsto_cornerGauge_error {ι : Type t} (l : Filter ι)
    (T : ι → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hT : ∀ xi : H, Tendsto (fun i => T i xi) l (𝓝 (U xi)))
    (hTs : ∀ xi : H, Tendsto (fun i => star (T i) xi) l (𝓝 (star U xi)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖T i‖ ≤ r) (phi : StrongDual ℂ A) :
    Tendsto (fun i => strongStarGauge (cornerFunctional pi hpi phi) (T i - U)) l (𝓝 0) := by
  have hX : ∀ xi : H, Tendsto (fun i => (T i - U) xi) l (𝓝 0) := by
    intro xi
    simpa only [ContinuousLinearMap.sub_apply, sub_self] using (hT xi).sub_const (U xi)
  have hXs : ∀ xi : H, Tendsto (fun i => star (T i - U) xi) l (𝓝 0) := by
    intro xi
    simpa only [star_sub, ContinuousLinearMap.sub_apply, sub_self] using
      (hTs xi).sub_const (star U xi)
  have hb : ∀ᶠ i in l, ‖T i - U‖ ≤ |r| + ‖U‖ := by
    filter_upwards [hr] with i hi
    exact (norm_sub_le (T i) U).trans (add_le_add_left (hi.trans (le_abs_self r)) _)
  exact tendsto_cornerGauge_zero pi hpi l (fun i => T i - U)
    hX hXs (|r| + ‖U‖) hb phi

/-- The C02 raw-state gauge is the concrete gauge of this *same* section. -/
theorem normalStateGauge_rawSection (phi : StateIndex A) (T : H →L[ℂ] H) :
    normalStateGauge phi (rawSection pi hpi T) =
      strongStarGauge (cornerFunctional pi hpi phi.val) T := by
  have h1 : arensProduct (bidualStar (rawSection pi hpi T)) (rawSection pi hpi T) =
      rawSection pi hpi (star T * T) := by
    change Model.toRaw A (star (sectionMap pi hpi T) * sectionMap pi hpi T) =
      Model.toRaw A (sectionMap pi hpi (star T * T))
    rw [section_mul, section_star]
  have h2 : arensProduct (rawSection pi hpi T) (bidualStar (rawSection pi hpi T)) =
      rawSection pi hpi (T * star T) := by
    change Model.toRaw A (sectionMap pi hpi T * star (sectionMap pi hpi T)) =
      Model.toRaw A (sectionMap pi hpi (T * star T))
    rw [section_mul, section_star]
  rw [normalStateGauge_eq_evaluation, h1, h2]
  rfl

/-- Source-state gauges of section errors tend to zero on the actual bounded
operator net. This discharges the previously separate concrete adapter. -/
theorem tendsto_normalStateGauge_section_error {ι : Type t} (l : Filter ι)
    (T : ι → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hT : ∀ xi : H, Tendsto (fun i => T i xi) l (𝓝 (U xi)))
    (hTs : ∀ xi : H, Tendsto (fun i => star (T i) xi) l (𝓝 (star U xi)))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖T i‖ ≤ r) (phi : StateIndex A) :
    Tendsto (fun i => normalStateGauge phi
      (rawSection pi hpi (T i) - rawSection pi hpi U)) l (𝓝 0) := by
  have h := tendsto_cornerGauge_error pi hpi l T U hT hTs r hr phi.val
  have hrw (i : ι) : normalStateGauge phi
      (rawSection pi hpi (T i) - rawSection pi hpi U) =
      strongStarGauge (cornerFunctional pi hpi phi.val) (T i - U) := by
    have hm : rawSection pi hpi (T i - U) =
        rawSection pi hpi (T i) - rawSection pi hpi U := by
      change Model.toRaw A (sectionMap pi hpi (T i - U)) =
        Model.toRaw A (sectionMap pi hpi (T i)) -
          Model.toRaw A (sectionMap pi hpi U)
      rw [(sectionMap pi hpi).map_sub, (Model.toRaw A).map_sub]
    rw [← hm, normalStateGauge_rawSection]
  simpa only [hrw] using h

/-- Finite simultaneity does not alter the net or its index. -/
theorem eventually_finite_cornerGauges_lt {ι : Type t} (l : Filter ι)
    (X : ι → H →L[ℂ] H)
    (hX : ∀ xi : H, Tendsto (fun i => X i xi) l (𝓝 0))
    (hXs : ∀ xi : H, Tendsto (fun i => star (X i) xi) l (𝓝 0))
    (r : ℝ) (hr : ∀ᶠ i in l, ‖X i‖ ≤ r)
    (s : Finset (StrongDual ℂ A)) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ i in l, ∀ phi ∈ s, strongStarGauge (cornerFunctional pi hpi phi) (X i) < eps := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall (by simp)
  | @insert phi s hnot ih =>
    have hphi := (tendsto_cornerGauge_zero pi hpi l X hX hXs r hr phi)
      (eventually_lt_nhds heps)
    filter_upwards [hphi, ih] with i hi hsi
    intro psi hpsi
    rcases Finset.mem_insert.mp hpsi with rfl | hs
    · exact hi
    · exact hsi psi hs

end MathlibAnnex.RepresentedCentralCorner
