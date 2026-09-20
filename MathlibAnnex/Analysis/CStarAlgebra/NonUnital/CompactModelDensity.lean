import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.MinimalProjectionDensity
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactImageOfRankOne

/-!
# The nonunital Rosenberg theorem below the continuum

A singleton irreducible representation with a dense subset smaller than the
continuum is faithful and its range is exactly the compact operators.  No
unit, simplicity, or faithfulness is assumed on the source.
-/

set_option autoImplicit false

open Set
open scoped Cardinal ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A small-density singleton model contains one represented rank-one projection. -/
theorem exists_norm_eq_one_and_map_eq_rankOne_of_singleton_of_dense
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∃ p : A, ∃ e : H, ‖e‖ = 1 ∧ pi p = InnerProductSpace.rankOne ℂ e e := by
  obtain ⟨p, hp, hpne, hcorner⟩ :=
    exists_nonzero_projection_scalar_corner_of_singleton_of_dense pi hsingle s hs hcard
  have hinj := injective_of_singleton pi hsingle
  have hpmap : pi p ≠ 0 := by
    intro hzero
    apply hpne
    apply hinj
    simpa using hzero
  obtain ⟨e, he, hmap⟩ :=
    exists_unitVector_map_eq_rankOne_of_scalar_corner pi hsingle.1 hp hpmap hcorner
  exact ⟨p, e, he, hmap⟩

/-- Every rank-one operator has a preimage in a small-density singleton model. -/
theorem exists_preimage_rankOne_of_singleton_of_dense
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    ∀ x y : H, ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y := by
  obtain ⟨p, e, he, hmap⟩ :=
    exists_norm_eq_one_and_map_eq_rankOne_of_singleton_of_dense pi hsingle s hs hcard
  exact exists_preimage_rankOne_of_rankOne_projection pi hsingle.1
    (injective_of_singleton pi hsingle) he hmap

/-- Generalized Rosenberg theorem, with equality to all compact operators,
not just the existence of one nonzero compact image. -/
theorem isCompactOperatorModel_of_singleton_of_dense
    [Nontrivial A] (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (s : Set H) (hs : Dense s) (hcard : #s < Cardinal.continuum) :
    IsCompactOperatorModel pi := by
  have hinj := injective_of_singleton pi hsingle
  have hpre := exists_preimage_rankOne_of_singleton_of_dense pi hsingle s hs hcard
  exact ⟨hinj, isCompactOperator_map_of_singleton_of_rankOne_preimages pi hsingle hpre,
    exists_preimage_of_isCompactOperator_of_rankOne_preimages pi hinj hpre⟩

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
