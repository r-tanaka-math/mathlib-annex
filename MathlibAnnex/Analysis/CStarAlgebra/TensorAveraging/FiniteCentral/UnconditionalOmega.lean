import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.Existence
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.OmegaCompactSelection
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.FiniteAverageRow

/-!
# The constructed finite averages supply one Ω and actual protected rows

C06, UNBUILT. These consumers REMOVE the displayed finite-average premise;
they do not change the canonical tensor norm, representation, vectors,
centrality orientation, or norm-one row budget.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped InnerProductSpace CStarAlgebra
namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.FiniteApproximation MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct.Algebra
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- One and the SAME point satisfies norm, all-test closure, all centrality
conditions and all off-diagonal matrix moments. -/
theorem exists_omega_from_constructed_averages
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi) :
    ∃ omega : StrongDual ℂ (StrongDual ℂ (Tensor A)),
      ‖omega‖ ≤ 1 ∧ InWeakStarClosure omega (rowConvexSet A) ∧
      (∀ (a : A) (f : StrongDual ℂ (Tensor A)),
        omega (f.comp (leftAction ℂ A a)) = omega (f.comp (rightAction ℂ A a))) ∧
      (∀ eta xi : H,
        omega (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) = inner ℂ eta xi) :=
  exists_omega_of_finiteCentralAverages pi hpi (hasFiniteCentralAverages pi hpi)

end MathlibAnnex.RepresentedCentralCorner

namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.RepresentedCentralCorner MathlibAnnex.CStarAlgebra.TensorAveraging
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- An exact finite row, not only a point in a weak closure. -/
theorem Representation.exists_finiteRow_from_constructed_averages
    (pi : Representation A H) (hpi : pi.IsIrreducible)
    (xi : H) (hxi : ‖xi‖ = 1) (F : Finset A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (x : Fin n → A),
      0 ≤ rowSquare A x ∧ ‖rowSquare A x‖ ≤ 1 ∧
      pi (rowSquare A x) xi = xi ∧
      ∀ a ∈ F, ∀ z : A,
        ‖a * rowMap A x z - rowMap A x z * a‖ ≤ epsilon * ‖z‖ :=
  pi.exists_finiteRow_of_finiteCentralAverages hpi
    (hasFiniteCentralAverages pi (Representation.isIrreducible_starAlgHom pi hpi))
    xi hxi F hepsilon

end MathlibAnnex.Analysis.CStarAlgebra
