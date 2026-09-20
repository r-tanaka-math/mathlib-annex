import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.OmegaCompactSelection
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.OmegaBridge

/-!
# Finite central averages to an actual protected finite row

The compact selection, all-test row closure and exact-rank-one adjustment
are composed here. The only upstream existence hypothesis is the explicit
finite central average boundary. It is not a premise called KOS or Omega.
C04 source candidate; the premise is still unproved at this checkpoint.
-/
set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
open MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarAlgebra.TensorAveraging
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- One exact row fixes the chosen vector, with the original operator-norm
budget, and protects ALL z simultaneously. -/
theorem Representation.exists_finiteRow_of_finiteCentralAverages
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (havg : HasFiniteCentralAverages pi (Representation.isIrreducible_starAlgHom pi hpi))
    (xi : H) (hxi : ‖xi‖ = 1) (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (x : Fin n → A),
      0 ≤ rowSquare A x ∧ ‖rowSquare A x‖ ≤ 1 ∧
      pi (rowSquare A x) xi = xi ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * rowMap A x z - rowMap A x z * a‖ ≤ epsilon * ‖z‖ := by
  obtain ⟨omega, hc, hb, hm⟩ := exists_omega_vector_of_finiteCentralAverages pi
    (Representation.isIrreducible_starAlgHom pi hpi) havg
  exact exists_finiteRow_exact_on_unital_vector A H pi hpi omega hc hb hm xi hxi F hepsilon

/-- G and delta are chosen BEFORE the comparison state and its later finite
accuracy request. The exact downstream PathCentralOn/pull conventions are
preserved without changing the transported unitary. -/
theorem Representation.exists_protected_state_transport_of_finiteCentralAverages
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (havg : HasFiniteCentralAverages pi (Representation.isIrreducible_starAlgHom pi hpi))
    (hno : pi.HasNoNonzeroCompactImage)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi) (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a : A, pi a = 0 → psi a = 0) →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧ ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  obtain ⟨omega, hc, hb, hm⟩ := exists_omega_vector_of_finiteCentralAverages pi
    (Representation.isIrreducible_starAlgHom pi hpi) havg
  exact pi.exists_protected_state_transport_of_omega hpi hno omega hc hb hm
    phi hphi hpure hker xi hxi hcoeff F hepsilon

end MathlibAnnex.Analysis.CStarAlgebra
