import MathlibAnnex.Topology.MetricSpace.DenseCardinality
import Mathlib.Tactic.NormNum
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterEigenvector

/-!
# Cardinality of character spaces in a singleton irreducible model

This is the cardinal, rather than countability, form of the joint-eigenvector
argument in `Representation.CharacterCountable`.  Irreducibility remains
part of the singleton hypothesis.  Faithful reducible models are not used.
-/

set_option autoImplicit false

open Function Metric Set
open scoped Cardinal ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- Joint eigenvectors belonging to distinct star characters are orthogonal. -/
theorem inner_eq_zero_of_ne_characters
    (pi : Representation A H) (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi psi : WeakDual.characterSpace ℂ D) (hne : chi ≠ psi)
    (x y : H) (hx : ∀ d : D, pi (d : A) x = chi d • x)
    (hy : ∀ d : D, pi (d : A) y = psi d • y) :
    inner ℂ x y = 0 := by
  obtain ⟨d, hd⟩ : ∃ d : D, chi d ≠ psi d := by
    by_contra h
    apply hne
    apply WeakDual.CharacterSpace.ext
    intro d
    by_contra hd
    exact h ⟨d, hd⟩
  have hadj : ContinuousLinearMap.adjoint (pi (d : A)) = pi (star (d : A)) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have heq := (pi (d : A)).adjoint_inner_right x y
  rw [hadj] at heq
  change inner ℂ x (pi ((star d : D) : A) y) = inner ℂ (pi (d : A) x) y at heq
  rw [hy (star d), hx d] at heq
  simp only [inner_smul_left, inner_smul_right, map_star] at heq
  by_contra hinner
  have hstar : star (psi d) = star (chi d) := mul_right_cancel₀ hinner heq
  exact hd (star_injective hstar).symm

/-- Distinct orthogonal unit vectors are uniformly separated. -/
theorem one_le_dist_of_norm_eq_one_of_inner_eq_zero
    {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = 0) :
    1 ≤ dist x y := by
  rw [dist_eq_norm]
  have hsq := norm_sub_mul_self (𝕜 := ℂ) x y
  rw [hxy, map_zero, hx, hy] at hsq
  norm_num at hsq
  nlinarith [norm_nonneg (x - y)]

/-- Character spaces of closed unital star subalgebras have cardinality
below the continuum when a singleton irreducible model has a dense subset
of cardinality below the continuum. -/
theorem cardinalMk_characterSpace_lt_continuum_of_singleton_of_dense
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] :
    #(WeakDual.characterSpace ℂ D) < Cardinal.continuum := by
  classical
  choose eta hn he using fun chi : WeakDual.characterSpace ℂ D =>
    exists_unit_eigenvector_of_character pi hsingle D chi
  apply MathlibAnnex.Topology.cardinalMk_lt_continuum_of_separated_of_dense
    s hs hcard eta (ε := 1) zero_lt_one
  intro chi psi hne
  exact one_le_dist_of_norm_eq_one_of_inner_eq_zero (hn chi) (hn psi)
    (inner_eq_zero_of_ne_characters pi D chi psi hne (eta chi) (eta psi)
      (he chi) (he psi))

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
