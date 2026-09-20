import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactModelDensity
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CyclicDensity

/-!
# Density lower bounds for counterexamples to Naimark's problem

The density conclusion of Akemann--Weaver, Proposition 6 (PNAS 101 (2004),
7525), is obtained here by a cardinal generalization of the Rosenberg route,
not by importing Glimm's CAR-subquotient theorem as a new premise.

The statement concerns every explicit norm-dense subset.  No continuum
hypothesis, cardinal-regularity assumption, or set-theoretic consistency
assertion is introduced.  No claim is made about arbitrary faithful reducible
representations of the algebra.
-/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- An algebra of norm density below the continuum with a singleton
irreducible model is an algebra of all compact operators. -/
theorem isCompactOperatorModel_of_singleton_of_dense_algebra
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set A) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    IsCompactOperatorModel pi := by
  obtain ⟨t, ht, htcard⟩ :=
    exists_dense_cardinalMk_lt_continuum_of_isIrreducible pi hsingle.1 s hs hcard
  exact isCompactOperatorModel_of_singleton_of_dense pi hsingle t ht htcard

/-- Every dense subset of an irreducible representation space of a
counterexample has cardinality at least the continuum. -/
theorem continuum_le_cardinalMk_dense_space_of_singleton_of_not_isCompactOperatorModel
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hnot : ¬ IsCompactOperatorModel pi) (s : Set H) (hs : Dense s) :
    Cardinal.continuum ≤ #s := by
  by_contra h
  exact hnot (isCompactOperatorModel_of_singleton_of_dense
    pi hsingle s hs (lt_of_not_ge h))

/-- The norm-density conclusion of Akemann--Weaver Proposition 6, for a
possibly nonunital algebra and independent Hilbert universe. -/
theorem continuum_le_cardinalMk_dense_algebra_of_singleton_of_not_isCompactOperatorModel
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hnot : ¬ IsCompactOperatorModel pi) (s : Set A) (hs : Dense s) :
    Cardinal.continuum ≤ #s := by
  by_contra h
  exact hnot (isCompactOperatorModel_of_singleton_of_dense_algebra
    pi hsingle s hs (lt_of_not_ge h))

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
