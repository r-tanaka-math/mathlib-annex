import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CharacterCountable
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterCardinality

/-!
# Cardinality of non-scalar characters

The exceptional scalar character of the unitization is excluded explicitly.
Only its complement is needed in the nonunital minimal-projection argument.
-/

set_option autoImplicit false

open Function Set
open scoped Cardinal ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- Non-scalar characters inject into any small dense subset of a singleton
irreducible model, up to the cardinal lifts. -/
theorem cardinalMk_nonScalarCharacterSpace_lt_continuum_of_singleton_of_dense
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum)
    (D : StarSubalgebra ℂ (Unitization ℂ A))
    [IsClosed (D : Set (Unitization ℂ A))] :
    #(NonScalarCharacterSpace (A := A) D) < Cardinal.continuum := by
  classical
  choose eta hn he using fun chi : NonScalarCharacterSpace (A := A) D =>
    exists_unit_eigenvector_of_character_ne_infinity pi hsingle D chi.1 chi.2
  apply MathlibAnnex.Topology.cardinalMk_lt_continuum_of_separated_of_dense
    s hs hcard eta (ε := 1) zero_lt_one
  intro chi psi hne
  have hval : chi.1 ≠ psi.1 := fun h => hne (Subtype.ext h)
  exact Representation.one_le_dist_of_norm_eq_one_of_inner_eq_zero (hn chi) (hn psi)
    (Representation.inner_eq_zero_of_ne_characters pi.unitization D chi.1 psi.1 hval
      (eta chi) (eta psi) (he chi) (he psi))

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
