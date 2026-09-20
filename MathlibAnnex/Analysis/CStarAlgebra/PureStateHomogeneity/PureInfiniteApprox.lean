import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SimpleRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GlobalState
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.GNSTwoLeg

/-! The Ω-independent approximate path field for infinite simple algebras. -/

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_gns_path_approx_of_simple_infinite
    (hsimple : IsSimpleCStarAlgebra A)
    (hinfinite : ¬ FiniteDimensional ℂ A)
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ u : unitary A, ∃ p : Path 1 u,
      ∀ a ∈ F, ‖pull phi u a - psi a‖ < epsilon := by
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
  have hinj : Function.Injective pi :=
    representation_injective_of_simple hsimple pi hirr
  have hno : pi.HasNoNonzeroCompactImage :=
    hasNoNonzeroCompactImage_representation_of_simple_infinite
      hsimple hinfinite pi hirr
  have hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi) := by
    intro a
    exact (inner_gnsStarAlgHom_stateGNSVector phi hstate a).symm
  have hker : ∀ a : A, pi a = 0 → psi a = 0 := by
    intro a ha
    have : a = 0 := hinj (by simpa using ha)
    simp [this]
  exact pi.exists_path_state_approx_of_essential
    (Representation.isIrreducible_starAlgHom pi hirr) hno
    phi xi hxi hcoeff psi hpsi.1 hpsi hker F hepsilon
end MathlibAnnex.CStarAlgebra
