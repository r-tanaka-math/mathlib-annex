import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRPermanence

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra

universe u v w

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

section Transport

variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- The Hilbert universe is independent of both algebra universes.
example
    (h : ∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
        NonUnitalStarAlgHom.range phi.gnsRepresentation)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) : ∃ a : A, pi a = T := by
  exact (NonUnitalStarAlgHom.mem_range pi).1
    (IsGCR.compact_le_range h pi hpi hT)

-- Surjective quotient permanence consumes literal pure GNS ranges.
example (h : IsGCR A) (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (phi : NonUnitalPureState B) (T : phi.GNS →L[ℂ] phi.GNS)
    (hT : IsCompactOperator T) : ∃ b : B, phi.gnsRepresentation b = T := by
  exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).1
    (h.of_surjective q hq phi hT)

example (h : IsGCR A) (q : A →⋆ₙₐ[ℂ] B) :
    IsGCR (HomKernelQuotient q) := h.hom_kernel_quotient q

example (h : IsGCR A) (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (phi : NonUnitalPureState (ClosedIdealQuotient.Quotient J hJ))
    (T : phi.GNS →L[ℂ] phi.GNS) (hT : IsCompactOperator T) :
    ∃ b : ClosedIdealQuotient.Quotient J hJ, phi.gnsRepresentation b = T :=
  (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).1
    (h.closed_ideal_quotient J hJ phi hT)

example (e : A ≃⋆ₐ[ℂ] B) (h : IsGCR A) : IsGCR B :=
  (isGCR_iff_of_starAlgEquiv e).1 h

set_option maxHeartbeats 1200000 in
-- The forward unitization branch also handles scalar quotient representations.
example (h : IsGCR A) :
    letI := _root_.CStarAlgebra.spectralOrder (Unitization ℂ A)
    letI := _root_.CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
    ∀ (phi : NonUnitalPureState (Unitization ℂ A)) (T : phi.GNS →L[ℂ] phi.GNS),
      IsCompactOperator T → ∃ z : Unitization ℂ A, phi.gnsRepresentation z = T := by
  letI := _root_.CStarAlgebra.spectralOrder (Unitization ℂ A)
  letI := _root_.CStarAlgebra.spectralOrderedRing (Unitization ℂ A)
  intro phi T hT
  exact (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).1 (h.unitization phi hT)

-- The reverse direction returns an element of A, not of its unitization.
example (h : IsGCR (Unitization ℂ A)) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    ∃ a : A, pi a = T :=
  (NonUnitalStarAlgHom.mem_range pi).1
    ((isGCR_of_unitization h).compact_le_range pi hpi hT)

example : IsGCR (Unitization ℂ A) ↔ IsGCR A := isGCR_unitization_iff

example [FiniteDimensional ℂ A] : IsGCR A := isGCR_of_finiteDimensional

example (h : IsGCR A) (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) : ∃ a : A, pi a ≠ 0 ∧ IsCompactOperator (pi a) :=
  h.exists_nonzero_compact_image pi hpi

end Transport

set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 1500000 in
-- No unit or separability assumption is imposed on the compact-operator algebra.
example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    letI := _root_.CStarAlgebra.spectralOrder (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
    letI := _root_.CStarAlgebra.spectralOrderedRing (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)
    ∀ phi : NonUnitalPureState (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H),
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
        NonUnitalStarAlgHom.range phi.gnsRepresentation :=
  isGCR_compactOperatorStarSubalgebra H

-- The same declaration includes a subsingleton Hilbert space.
example (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Subsingleton H] :
    IsGCR (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :=
  isGCR_compactOperatorStarSubalgebra H
