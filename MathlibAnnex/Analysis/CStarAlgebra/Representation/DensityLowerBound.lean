import Mathlib.Tactic.FunProp
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactModelDensity
import MathlibAnnex.Analysis.CStarAlgebra.Representation.OrdinarySingleton
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.DensityLowerBound

/-!
# Unital and ordinary-representation density endpoints

These interfaces specialize the density argument to unital source algebras
while retaining the original quantifier over ordinary nonzero irreducible
representations.  The unit need not be explicitly preserved by competitors.
-/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- The density version of the ordinary-competitor Rosenberg conclusion. -/
theorem isCompactOperatorModel_of_singleton_amongNonUnital_of_dense
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    IsCompactOperatorModel pi.toNonUnitalStarAlgHom :=
  isCompactOperatorModel_of_singleton_of_dense pi hsingle.isSingletonIrreducibleModel s hs hcard

/-- Dense subsets of an infinite-dimensional unital singleton model cannot
have cardinality below the continuum. -/
theorem continuum_le_cardinalMk_dense_space_of_singleton_of_not_finiteDimensional
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hA : ¬ FiniteDimensional ℂ A) (s : Set H) (hs : Dense s) :
    Cardinal.continuum ≤ #s := by
  by_contra h
  exact hA (finiteDimensional_algebra_of_singleton_of_dense
    pi hsingle s hs (lt_of_not_ge h))

/-- A small dense subset of a unital algebra gives a small dense subset of
any nonzero irreducible model by continuity of one nonzero vector's orbit. -/
theorem exists_dense_cardinalMk_lt_continuum_of_isIrreducible
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    (s : Set A) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ t : Set H, Dense t ∧ #t < Cardinal.continuum := by
  letI : Nontrivial H := nontrivial_of_isNonzero pi hirr.1
  obtain ⟨x, hx⟩ : ∃ x : H, x ≠ 0 := exists_ne 0
  have horbit := denseRange_orbitMap_of_isIrreducible pi hirr hx
  have hcont : Continuous (fun a : A => pi a x) := by fun_prop
  exact MathlibAnnex.Topology.exists_dense_cardinalMk_lt_continuum_of_continuous_denseRange
    (fun a : A => pi a x) hcont horbit s hs hcard

/-- The algebra's norm-density lower bound in the unital infinite-dimensional case. -/
theorem continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_finiteDimensional
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hA : ¬ FiniteDimensional ℂ A) (s : Set A) (hs : Dense s) :
    Cardinal.continuum ≤ #s := by
  by_contra h
  obtain ⟨t, ht, htcard⟩ := exists_dense_cardinalMk_lt_continuum_of_isIrreducible
    pi hsingle.1 s hs (lt_of_not_ge h)
  exact hA (finiteDimensional_algebra_of_singleton_of_dense pi hsingle t ht htcard)

/-- The same lower bound with all ordinary possibly nonunital competitors included. -/
theorem continuum_le_cardinalMk_dense_algebra_of_singleton_amongNonUnital_of_not_finiteDimensional
    [Nontrivial A] (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModelAmongNonUnital.{u, v, u} pi)
    (hA : ¬ FiniteDimensional ℂ A) (s : Set A) (hs : Dense s) :
    Cardinal.continuum ≤ #s :=
  continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_finiteDimensional
    pi hsingle.isSingletonIrreducibleModel hA s hs

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
