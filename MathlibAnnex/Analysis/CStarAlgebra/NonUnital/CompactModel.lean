import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactExclusion
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.CompactRange
import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal

/-!
# Compact-operator models for genuinely non-unital C-star algebras

This file assembles the non-unital Rosenberg conclusion.  No unit is assumed
on the source algebra.  `NonUnital.CompactExclusion` proves directly that
every represented operator is compact, while `NonUnital.CompactRange` proves
the reverse range inclusion.  The older simplicity-based closure is retained
below as an independent conditional route.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A separable singleton irreducible representation of a nonzero possibly
non-unital complex C-star algebra is an exact model of the compact operators.
Neither simplicity nor faithfulness is assumed. -/
theorem isCompactOperatorModel_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    IsCompactOperatorModel pi := by
  exact ⟨injective_of_singleton pi hsingle,
    isCompactOperator_map_of_singleton pi hsingle,
    exists_preimage_of_compact_singleton pi hsingle⟩

/-- Faithfulness and equality of the represented range with all compact
operators for a genuinely non-unital singleton model. -/
theorem faithful_and_compactOperatorModel_of_singleton [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    Function.Injective pi ∧ IsCompactOperatorModel pi :=
  ⟨injective_of_singleton pi hsingle,
    isCompactOperatorModel_of_singleton pi hsingle⟩

/-- Closed-ideal simplicity turns the one nonzero compact image supplied by
the singleton argument into compactness of the entire represented image. -/
theorem isCompactOperator_map_of_singleton_of_isSimple [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hsimple : IsSimpleCStarAlgebra A) :
    ∀ a : A, IsCompactOperator (pi a) := by
  obtain ⟨p, _hp, hpne, _hrankOne, hpcompact⟩ :=
    exists_nonzero_projection_rankOne_map pi hsingle
  let I : TwoSidedIdeal A :=
    MathlibAnnex.CStarAlgebra.compactPreimageIdeal pi
  have hpI : p ∈ I :=
    (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal pi p).2 hpcompact
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hpzero : p = 0 := by
      rw [hbot] at hpI
      simpa using hpI
    exact hpne hpzero
  have hItop : I = ⊤ :=
    (hsimple.2 I
      (MathlibAnnex.CStarAlgebra.isClosed_compactPreimageIdeal pi)).resolve_left hIne
  intro a
  have haI : a ∈ I := by
    rw [hItop]
    trivial
  exact (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal pi a).1 haI

/-- Conditional closure of the genuinely non-unital compact-operator model:
the only extra input is norm-closed two-sided simplicity of `A`. -/
theorem isCompactOperatorModel_of_singleton_of_isSimple [Nontrivial A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hsimple : IsSimpleCStarAlgebra A) :
    IsCompactOperatorModel pi := by
  refine ⟨injective_of_singleton pi hsingle,
    isCompactOperator_map_of_singleton_of_isSimple pi hsingle hsimple, ?_⟩
  exact exists_preimage_of_compact_singleton pi hsingle

/-- Faithfulness and exact compact range, conditionally on the generic
non-unital simplicity bridge. -/
theorem faithful_and_compactOperatorModel_of_singleton_of_isSimple
    [Nontrivial A] [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (hsimple : IsSimpleCStarAlgebra A) :
    Function.Injective pi ∧ IsCompactOperatorModel pi :=
  ⟨injective_of_singleton pi hsingle,
    isCompactOperatorModel_of_singleton_of_isSimple pi hsingle hsimple⟩

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
