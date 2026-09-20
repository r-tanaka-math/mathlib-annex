import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.FiniteAverageRow
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.InfiniteRowConditional
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.FiniteTransport
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.ConditionalGlobal

/-!
# The exact remaining finite-average interface to the same-alpha KOS target

This is not an unconditional proof of KOS: HasRepresentationAverages is
explicitly assigned to the other source-author chat, not silently assumed
available. Compact selection and all protected row fields have proof bodies
in the controller source. Both simple finite and simple infinite cases are
included here; same-kernel nonsimple/nonunital scope is still separate.
C04 source candidate, unbuilt.
-/
set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarAlgebra MathlibAnnex.CStarAlgebra.TensorAveraging
universe u
variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- It is sufficient here to have all representations in the GNS universe.
The assigned analytic/geometric theorem is requested with independent H. -/
def HasRepresentationAverages : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H],
    ∀ (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi),
      HasFiniteCentralAverages pi hpi

/-- Actual GNS specialization supplies the row field with its original
nonlinear epsilon budget, not merely an isomorphic auxiliary model. -/
theorem pureGNSRowSupplier_of_representationAverages
    (havg : HasRepresentationAverages A) : PureGNSProtectedRowSupplier A := by
  intro phi hpure F epsilon hepsilon
  let hstate : phi ∈ stateSpace A := hpure.1
  let f := positiveLinearMapOfMemStateSpace phi hstate
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi := stateGNSVector phi hstate
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hstate
  have hxi0 : xi ≠ 0 := by intro hz; simp [hz] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : pi.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom pi).mpr
      (isIrreducible_pureState_gnsStarAlgHom phi hstate hpure)
  have ha := havg f.GNS pi (Representation.isIrreducible_starAlgHom pi hirr)
  have hb : 0 < (epsilon / 2) / (8 * Real.pi) := by positivity
  obtain ⟨n, x, hpos, hn, hfix, hcomm⟩ :=
    pi.exists_finiteRow_of_finiteCentralAverages hirr ha xi hxi F hb
  exact ⟨n, x, hn, hfix, hcomm⟩

/-- All four path transport fields, both dimension cases. -/
theorem finitePathTransport_pure_of_representationAverages
    (havg : HasRepresentationAverages A) (hsimple : IsSimpleCStarAlgebra A) :
    FinitePathTransport (IsPureState A) := by
  by_cases hfin : FiniteDimensional ℂ A
  · letI : FiniteDimensional ℂ A := hfin
    exact finitePathTransport_pure_of_simple_finite hsimple
  · exact finitePathTransport_pure_infinite_of_rowSupplier hsimple hfin
      (pureGNSRowSupplier_of_representationAverages A havg)

/-- This terminal implication names the ORIGINAL KOSStmt and obtains the
state equation and approximate-inner witnesses from the same alpha.
The finite-average existence theorem is not supplied by this file. -/
theorem kishimotoOzawaSakaiProperty_of_representationAverages
    (havg : ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
      HasRepresentationAverages A) : KishimotoOzawaSakaiProperty.{u} := by
  apply kishimotoOzawaSakaiProperty_of_pure_finitePathTransport
  intro A _ _ _ _ hsimple
  exact finitePathTransport_pure_of_representationAverages A (havg A) hsimple

end MathlibAnnex.CStarAlgebra
