import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RankOneRow
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.ProtectedState
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters

/-!
# Conditional Ω-to-protected-state bridge

This file checks the complete consumer connection once Ω is available. The
three Ω properties are hypotheses, so this theorem is not a general supplier.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.FiniteApproximation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

theorem Representation.exists_protected_state_transport_of_omega
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (hno : pi.HasNoNonzeroCompactImage)
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ v : H,
      omega (vectorMoment A H pi.toNonUnitalStarAlgHom v) = (‖v‖ ^ 2 : ℂ))
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hpure : IsPureState A phi)
    (hker : ∀ a : A, pi a = 0 → phi a = 0)
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi (pi a xi))
    (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
      ∀ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A → IsPureState A psi →
        (∀ a : A, pi a = 0 → psi a = 0) →
        (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
        ∀ T : Finset A, ∀ eta : ℝ, 0 < eta →
          ∃ u : unitary A, ∃ p : Path 1 u,
            PathCentralOn p F epsilon ∧
              ∀ a ∈ T, ‖pull phi u a - psi a‖ < eta := by
  have hbudget : 0 < (epsilon / 2) / (8 * Real.pi) := by positivity
  obtain ⟨n, x, _hpos, hq, hqxi, hprotect⟩ :=
    exists_finiteRow_exact_on_unital_vector A H pi hpi omega homega hcentral
      hmoment xi hxi F hbudget
  exact pi.exists_protected_state_transport_of_row
    (Representation.isIrreducible_starAlgHom pi hpi) hno
    phi hphi hpure hker xi hxi hcoeff F hepsilon x hq hqxi hprotect

end MathlibAnnex.Analysis.CStarAlgebra
