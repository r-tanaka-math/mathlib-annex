import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARObstruction

set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.CAR

universe u

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 900000 in
-- This is the fixed CAR completion, with no independently supplied representation.
example : ¬ (∀ phi : NonUnitalPureState Limit,
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
      NonUnitalStarAlgHom.range phi.gnsRepresentation) :=
  not_isGCR_limit

-- This is the independent closed-ideal-quotient predicate, not a definition by GCR.
example : ¬ IsInternalTypeI Limit := not_isInternalTypeI_limit

-- The nonunital representation map is not assumed to preserve 1.
example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation Limit H) (hpi : pi.IsIrreducible)
    (a : Limit) (ha : IsCompactOperator (pi a)) : a = 0 :=
  eq_zero_of_isCompactOperator_nonunital_image pi hpi ha

example {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation Limit H) (hpi : pi.IsIrreducible) :
    ¬ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi :=
  not_compact_le_range_nonunital pi hpi

example {A : Type u} [NonUnitalCStarAlgebra A]
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] Limit) (hq : Function.Surjective q) : ¬ IsGCR A :=
  not_isGCR_of_subquotient D q hq

example {A : Type u} [NonUnitalCStarAlgebra A]
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] Limit) (hq : Function.Surjective q) : ¬ IsInternalTypeI A :=
  not_isInternalTypeI_of_subquotient D q hq
