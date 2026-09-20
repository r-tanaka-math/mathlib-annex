import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.UniversalStarNet
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.StateBidualNormal

/-!
# Actual simultaneous state-gauge approximants

C01 gave gauge identities conditional on convergence of GNS vectors. This
file supplies a single source net with those convergences for every state
at once, as well as all scalar weak-star tests. States are indexed as a
subtype, so the zero algebra is allowed: no normalized state is selected
from an empty state space.

This is a universal-family statement, not yet transfer of normality to an
unrelated irreducible corner. C02 unbuilt proof-source candidate.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProduct ComplexOrder

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev StateIndex (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] := {phi : A →L[ℂ] ℂ // phi ∈ stateSpace A}

abbrev StateHilbert (phi : StateIndex A) :=
  (positiveLinearMapOfMemStateSpace phi.val phi.property).GNS

def stateFamily (phi : StateIndex A) :
    A →⋆ₙₐ[ℂ] (StateHilbert phi →L[ℂ] StateHilbert phi) :=
  (positiveLinearMapOfMemStateSpace phi.val phi.property).gnsStarAlgHom.toNonUnitalStarAlgHom

abbrev StateApproxIndex (A : Type u) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :=
  UniversalIndex (A := A) (StateHilbert (A := A))

/-- A single chosen net for every source state, not one net per state. -/
def stateSourceNet (F : StrongDual ℂ (StrongDual ℂ A))
    (d : StateApproxIndex A) : A :=
  universalSample (StateHilbert (A := A)) stateFamily F d

theorem stateSourceNet_norm_le (F : StrongDual ℂ (StrongDual ℂ A))
    (d : StateApproxIndex A) : ‖stateSourceNet F d‖ ≤ ‖F‖ :=
  universalSample_norm_le (StateHilbert (A := A)) stateFamily F d

theorem stateSourceNet_weakStar (F : StrongDual ℂ (StrongDual ℂ A)) :
    Tendsto (fun d => StrongDual.toWeakDual
      (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d))) atTop
      (𝓝 (StrongDual.toWeakDual F)) :=
  universalSample_weakStar (StateHilbert (A := A)) stateFamily F

/-- The error is in the fixed Banach bidual, with the same sample on both
sides of every star-square. -/
def stateSourceError (F : StrongDual ℂ (StrongDual ℂ A))
    (d : StateApproxIndex A) : StrongDual ℂ (StrongDual ℂ A) :=
  NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d) - F

@[simp] theorem extension_stateSourceError
    (F : StrongDual ℂ (StrongDual ℂ A)) (d : StateApproxIndex A)
    (phi : StateIndex A) :
    extension (stateFamily phi) (stateSourceError F d) =
      stateFamily phi (stateSourceNet F d) - extension (stateFamily phi) F := by
  calc
    _ = extension (stateFamily phi)
        (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d) - F) := rfl
    _ = extension (stateFamily phi)
          (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)) -
          extension (stateFamily phi) F :=
      map_sub (extension (stateFamily phi)) _ _
    _ = _ := by rw [extension_canonical]

/-- Actual forward-vector error convergence in each state's own GNS. -/
theorem stateSourceError_forward (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) (xi : StateHilbert phi) :
    Tendsto (fun d => extension (stateFamily phi) (stateSourceError F d) xi)
      atTop (𝓝 0) := by
  have h := (universalSample_strongStar (StateHilbert (A := A)) stateFamily F phi xi).1
  have hs := h.sub_const (extension (stateFamily phi) F xi)
  simpa [stateSourceNet, extension_stateSourceError] using hs

/-- Actual adjoint-vector error convergence, not reuse of the forward gauge. -/
theorem stateSourceError_backward (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) (xi : StateHilbert phi) :
    Tendsto (fun d => extension (stateFamily phi) (bidualStar (stateSourceError F d)) xi)
      atTop (𝓝 0) := by
  have h := (universalSample_strongStar (StateHilbert (A := A)) stateFamily F phi xi).2
  have hs := h.sub_const (star (extension (stateFamily phi) F) xi)
  simpa [stateSourceNet, extension_bidualStar, extension_stateSourceError,
    star_sub, map_star] using hs

/-- Every positive star-square error gauge tends to zero along one net. -/
theorem stateSourceNet_leftGauge (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) :
    Tendsto (fun d => stateExtension phi.val
      (arensProduct (bidualStar (stateSourceError F d)) (stateSourceError F d)))
      atTop (𝓝 0) := by
  apply tendsto_stateExtension_star_square atTop phi.val phi.property
  exact stateSourceError_forward F phi (stateGNSVector phi.val phi.property)

/-- The reverse positive square has its own proved convergence. -/
theorem stateSourceNet_rightGauge (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) :
    Tendsto (fun d => stateExtension phi.val
      (arensProduct (stateSourceError F d) (bidualStar (stateSourceError F d))))
      atTop (𝓝 0) := by
  have h := tendsto_stateExtension_star_square atTop phi.val phi.property
    (fun d => bidualStar (stateSourceError F d))
    (stateSourceError_backward F phi (stateGNSVector phi.val phi.property))
  simpa only [bidualStar_bidualStar] using h

/-- Finitely many left and right gauges can be made small at the same index.
This is a common-index conclusion, with no independent statewise choices. -/
theorem stateSourceNet_finite_gauges (F : StrongDual ℂ (StrongDual ℂ A))
    (s : Finset (StateIndex A)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d in (atTop : Filter (StateApproxIndex A)), ∀ phi ∈ s,
      ‖stateExtension phi.val
        (arensProduct (bidualStar (stateSourceError F d)) (stateSourceError F d))‖ < ε ∧
      ‖stateExtension phi.val
        (arensProduct (stateSourceError F d) (bidualStar (stateSourceError F d)))‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert phi s hnot ih =>
      have hl := (Metric.tendsto_nhds.mp (stateSourceNet_leftGauge F phi)) ε hε
      have hr := (Metric.tendsto_nhds.mp (stateSourceNet_rightGauge F phi)) ε hε
      filter_upwards [ih, hl, hr] with d hd hleft hright
      intro psi hpsi
      rcases Finset.mem_insert.mp hpsi with rfl | hmem
      · exact ⟨by simpa using hleft, by simpa using hright⟩
      · exact hd psi hmem

end MathlibAnnex.RepresentedBidual
