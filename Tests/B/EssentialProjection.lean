import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.EssentialProjection

/-!
Typed consumers of the actual essential projection, including degenerate
actions.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.EssentialProjectionConsumers

open NonUnitalCStarRepresentation

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- An arbitrary action has the proved star projection onto its actual
closed essential subspace; no nonzero or nondegeneracy premise is present. -/
example (pi : NonUnitalCStarRepresentation A H) :
    IsStarProjection pi.essentialProjection ∧
      pi.essentialProjection.range =
        (Submodule.span ℂ (Set.range (fun p : A × H => pi p.1 p.2))).topologicalClosure :=
  ⟨isStarProjection_essentialProjection pi, range_essentialProjection pi⟩

example (pi : NonUnitalCStarRepresentation A H) :
    ∃ (_ : pi.essentialSubspace.HasOrthogonalProjection),
      pi.essentialProjection = pi.essentialSubspace.starProjection :=
  essentialProjection_eq_starProjection pi

example (pi : NonUnitalCStarRepresentation A H) (a : A) (x : H) :
    IsClosed (pi.essentialSubspace : Set H) ∧ pi a x ∈ pi.essentialSubspace :=
  ⟨isClosed_essentialSubspace pi, apply_mem_essentialSubspace pi a x⟩

example (pi : NonUnitalCStarRepresentation A H) (x : H) :
    pi.essentialProjection x = 0 ↔ ∀ a : A, pi a x = 0 :=
  essentialProjection_apply_eq_zero_iff pi x

example (pi : NonUnitalCStarRepresentation A H) :
    pi.essentialProjection = 0 ↔ ∀ a : A, pi a = 0 :=
  essentialProjection_eq_zero_iff pi

example (pi : NonUnitalCStarRepresentation A H) :
    pi.essentialProjection = 1 ↔ pi.IsNondegenerate :=
  essentialProjection_eq_one_iff pi

example (pi : NonUnitalCStarRepresentation A H) (a : A) :
    pi.essentialProjection * pi a = pi a ∧ pi a * pi.essentialProjection = pi a :=
  ⟨essentialProjection_mul pi a, mul_essentialProjection pi a⟩

/-- Membership and centrality refer to the same generated algebra on H. -/
example (pi : NonUnitalCStarRepresentation A H) :
    pi.essentialProjection ∈ VonNeumannAlgebra.generated pi.unitization.range ∧
      ∀ T : H →L[ℂ] H, T ∈ VonNeumannAlgebra.generated pi.unitization.range →
        T * pi.essentialProjection = pi.essentialProjection * T :=
  ⟨essentialProjection_mem_generated pi, essentialProjection_commute pi⟩

end MathlibAnnex.Analysis.CStarAlgebra.EssentialProjectionConsumers
