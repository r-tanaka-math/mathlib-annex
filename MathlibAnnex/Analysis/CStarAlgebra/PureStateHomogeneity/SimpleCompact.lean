import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SimpleRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.CompactPath

/-! The compact-image protected local path for a simple finite-dimensional algebra. -/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem exists_protected_state_transport_of_simple_finite
    (hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A]
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  letI : FiniteDimensional ℂ H :=
    finiteDimensional_representation_space_of_finiteDimensional_algebra pi hpi
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hpi
  have hsurj : Function.Surjective pi :=
    representation_surjective_of_simple_finiteDimensional hsimple pi hpi
  exact pi.exists_protected_state_transport_of_full_finite hinj hsurj
    (Representation.isIrreducible_starAlgHom pi hpi)
    phi hphi xi hxi hcoeff F hepsilon

end MathlibAnnex.CStarAlgebra
