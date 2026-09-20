import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SimpleCompact
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GNSTwoLeg
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.CompactGlobal

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_gns_protected_transport_of_simple_finite
    (hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A]
    (phi : A →L[ℂ] ℂ) (hpure : IsPureState A phi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  let hphi : phi ∈ stateSpace A := hpure.1
  let f := positiveLinearMapOfMemStateSpace phi hphi
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector phi hphi
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hphi
  have hxi0 : xi ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : pi.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom pi).mpr
      (isIrreducible_pureState_gnsStarAlgHom phi hphi hpure)
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) := by
    intro a
    exact (inner_gnsStarAlgHom_stateGNSVector phi hphi a).symm
  exact CStarAlgebra.exists_protected_state_transport_of_simple_finite
    hsimple pi hirr phi hphi xi hxi hcoeff F hepsilon

/-- Exact state transport between arbitrary pure states in a finite-dimensional
simple algebra, by one path starting at the identity. -/
theorem pure_gns_path_pull_eq_of_simple_finite
    (hsimple : IsSimpleCStarAlgebra A) [FiniteDimensional ℂ A]
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) (hpsi : IsPureState A psi) :
    ∃ u : unitary A, ∃ p : Path 1 u, pull phi u = psi := by
  let hstate : phi ∈ stateSpace A := hphi.1
  let f := positiveLinearMapOfMemStateSpace phi hstate
  let pi : Representation A f.GNS := f.gnsStarAlgHom
  let xi : f.GNS := stateGNSVector phi hstate
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector phi hstate
  have hxi0 : xi ≠ 0 := by
    intro hzero
    simp [hzero] at hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi0
  have hirr : pi.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom pi).mpr
      (isIrreducible_pureState_gnsStarAlgHom phi hstate hphi)
  letI : FiniteDimensional ℂ f.GNS :=
    finiteDimensional_representation_space_of_finiteDimensional_algebra pi hirr
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hirr
  have hsurj : Function.Surjective pi :=
    representation_surjective_of_simple_finiteDimensional hsimple pi hirr
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) := by
    intro a
    exact (inner_gnsStarAlgHom_stateGNSVector phi hstate a).symm
  exact pi.exists_path_pull_eq_of_full_finite hinj hsurj
    phi psi hpsi.1 hpsi xi hxi hcoeff
end MathlibAnnex.CStarAlgebra
