import MathlibAnnex.Analysis.Normed.Operator.Cardinality
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation

/-! # Cardinal upper bounds for faithfully separably represented algebras -/
set_option autoImplicit false
open scoped Cardinal
namespace MathlibAnnex.Analysis.CStarAlgebra
universe u v
variable {A : Type u} {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H]

/-- A faithful ordinary representation on a separable Hilbert space bounds
the cardinality of the possibly nonunital source algebra by the continuum. -/
theorem NonUnitalCStarRepresentation.cardinalMk_le_continuum_of_injective
    [NonUnitalCStarAlgebra A] (pi : NonUnitalCStarRepresentation A H)
    (hpi : Function.Injective pi) : #A ≤ Cardinal.continuum :=
  MathlibAnnex.Topology.cardinalMk_le_continuum_of_injective pi hpi
    (MathlibAnnex.cardinalMk_continuousLinearMap_le_continuum H)

/-- The unital counterpart of the faithful separable-representation bound. -/
theorem Representation.cardinalMk_le_continuum_of_injective
    [CStarAlgebra A] (pi : Representation A H) (hpi : Function.Injective pi) :
    #A ≤ Cardinal.continuum :=
  NonUnitalCStarRepresentation.cardinalMk_le_continuum_of_injective
    pi.toNonUnitalStarAlgHom hpi

end MathlibAnnex.Analysis.CStarAlgebra
