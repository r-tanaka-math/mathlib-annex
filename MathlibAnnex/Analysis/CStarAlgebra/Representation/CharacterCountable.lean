import Mathlib.Topology.Bases
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterEigenvector

/-!
# Countability of represented character spaces

Distinct characters give orthogonal joint unit eigenvectors.  A separable
Hilbert space cannot contain uncountably many such vectors.
-/

set_option autoImplicit false

open Function Metric Set
open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- If every character of a closed star subalgebra is realized by a joint
unit eigenvector in a separable Hilbert space, its character space is
countable.  The singleton hypothesis supplies those vectors via pure GNS
representations. -/
theorem countable_characterSpace_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    Countable (WeakDual.characterSpace ℂ D) := by
  choose eta heta_norm heta_eigen using fun chi : WeakDual.characterSpace ℂ D =>
    exists_unit_eigenvector_of_character pi hsingle D chi
  have horth : Pairwise fun chi psi : WeakDual.characterSpace ℂ D =>
      inner ℂ (eta chi) (eta psi) = 0 := by
    intro chi psi hne
    obtain ⟨d, hd⟩ : ∃ d : D, chi d ≠ psi d := by
      by_contra hall
      push Not at hall
      exact hne (WeakDual.CharacterSpace.ext hall)
    have hadj : ContinuousLinearMap.adjoint (pi (d : A)) = pi (star (d : A)) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    have heq := (pi (d : A)).adjoint_inner_right (eta chi) (eta psi)
    rw [hadj] at heq
    change inner ℂ (eta chi) (pi ((star d : D) : A) (eta psi)) =
      inner ℂ (pi (d : A) (eta chi)) (eta psi) at heq
    rw [heta_eigen psi (star d), heta_eigen chi d] at heq
    simp only [inner_smul_left, inner_smul_right, map_star] at heq
    by_contra hinner
    have hstar : star (psi d) = star (chi d) :=
      mul_right_cancel₀ hinner heq
    exact hd (star_injective hstar).symm
  have hdist (chi psi : WeakDual.characterSpace ℂ D) (hne : chi ≠ psi) :
      1 ≤ dist (eta chi) (eta psi) := by
    rw [dist_eq_norm]
    have hsq := norm_sub_mul_self (𝕜 := ℂ) (eta chi) (eta psi)
    rw [horth hne, map_zero, heta_norm chi, heta_norm psi] at hsq
    norm_num at hsq
    nlinarith [norm_nonneg (eta chi - eta psi)]
  have hballs : Pairwise (Disjoint on fun chi : WeakDual.characterSpace ℂ D =>
      ball (eta chi) (1 / 3 : ℝ)) := by
    intro chi psi hne
    apply ball_disjoint_ball
    have := hdist chi psi hne
    norm_num at this ⊢
    linarith
  exact hballs.countable_of_isOpen_disjoint
    (fun _ => isOpen_ball)
    (fun chi => ⟨eta chi, mem_ball_self (by norm_num)⟩)

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
