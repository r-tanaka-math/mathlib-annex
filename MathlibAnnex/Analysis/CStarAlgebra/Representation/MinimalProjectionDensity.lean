import MathlibAnnex.Topology.CompactCardinality
import MathlibAnnex.Analysis.CStarAlgebra.Representation.MinimalProjection
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CharacterCardinality

/-! # Minimal projections from a singleton model of density below the continuum -/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder IsMulCommutative

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- The cardinal version of the unital minimal-projection theorem. -/
theorem exists_nonzero_projection_scalar_corner_of_singleton_of_dense [Nontrivial A]
    (pi : Representation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ p : A, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ a : A, ∃ c : ℂ, p * a * p = c • p := by
  obtain ⟨D, hD⟩ := exists_maximalAbelian (A := A)
  letI : IsClosed (D : Set A) := hD.isClosed
  letI : IsMulCommutative D := hD.1
  letI : CommCStarAlgebra D := {}
  have hsmall := cardinalMk_characterSpace_lt_continuum_of_singleton_of_dense
    pi hsingle s hs hcard D
  obtain ⟨chi, hchi⟩ :=
    MathlibAnnex.Topology.exists_isOpen_singleton_of_cardinalMk_lt_continuum hsmall
  obtain ⟨p, hp, hpne, hpd⟩ :=
    exists_projection_mul_eq_smul_of_isOpen_singleton chi hchi
  refine ⟨(p : A), hp.map D.subtype, ?_,
    corner_eq_smul_of_maximalAbelian D hD chi p hp hpd⟩
  intro hzero
  apply hpne
  apply Subtype.ext
  exact hzero

end Representation
end MathlibAnnex.Analysis.CStarAlgebra
