/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRPermanence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRCharacterization
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NonUnitalGCRSubalgebra
import MathlibAnnex.Analysis.CStarAlgebra.CAR.NoCompacts

/-!
# The fixed CAR algebra is not GCR

The CAR algebra is the existing completion `MathlibAnnex.CStarAlgebra.CAR.Limit`.
Its simplicity, infinite dimensionality, pure root state and absence of
nonzero compact images are reused. No inductive limit is reconstructed here.

The unital no-compacts theorem is first transported to the genuinely nonunital
representation interface: nonzero irreducibility proves preservation of the
unit. A nonzero rank-one operator then rules out compact containment. The
directly proved pure root state provides an actual irreducible representation,
so the final obstruction has no existential representation hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Set InnerProductSpace
open MathlibAnnex.Analysis.CStarAlgebra
open scoped ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The old unital CAR theorem applies to any nonzero irreducible nonunital
representation, since the existing bridge proves that it preserves `1`. -/
theorem eq_zero_of_isCompactOperator_nonunital_image
    (pi : NonUnitalCStarRepresentation Limit H) (hpi : pi.IsIrreducible)
    {a : Limit} (ha : IsCompactOperator (pi a)) : a = 0 := by
  have hpi' : NonUnitalRepresentation.IsIrreducible pi := hpi
  exact eq_zero_of_isCompactOperator_image
    (NonUnitalRepresentation.toUnital pi hpi')
    (NonUnitalRepresentation.isIrreducible_toUnital pi hpi') ha

/-- Every nonzero irreducible CAR image fails to contain all compact operators.
The proof uses a concrete nonzero rank-one operator in the given Hilbert space. -/
theorem not_compact_le_range_nonunital
    (pi : NonUnitalCStarRepresentation Limit H) (hpi : pi.IsIrreducible) :
    ¬ ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≤
      NonUnitalStarAlgHom.range pi := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  intro hcompact
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range pi).1
    (hcompact (MathlibAnnex.Analysis.CStarAlgebra.isCompactOperator_rankOne x x))
  have hac : IsCompactOperator (pi a) := by
    rw [ha]
    exact MathlibAnnex.Analysis.CStarAlgebra.isCompactOperator_rankOne x x
  have ha0 : a = 0 := eq_zero_of_isCompactOperator_nonunital_image pi hpi hac
  have hzero : rankOne ℂ x x = 0 := by
    rw [← ha, ha0, map_zero]
  exact (rankOne_ne_zero (𝕜 := ℂ) hx hx) hzero

/-- The existing CAR completion is not GCR. The nonzero irreducible witness
is the GNS action of its explicitly constructed pure product-vector state. -/
theorem not_isGCR_limit : ¬ IsGCR Limit := by
  let f := positiveLinearMapOfMemStateSpace rootState rootState_mem_stateSpace
  let rho : Representation Limit f.GNS := f.gnsStarAlgHom
  have hnorm : ‖f.gnsCyclicVector‖ = 1 :=
    PositiveLinearMap.norm_gnsCyclicVector f
      (positiveLinearMapOfMemStateSpace_one rootState rootState_mem_stateSpace)
  have hne : f.gnsCyclicVector ≠ 0 := by
    intro hzero
    simpa [hzero] using hnorm
  letI : Nontrivial f.GNS := nontrivial_of_ne f.gnsCyclicVector 0 hne
  have hrho : rho.IsIrreducible :=
    (Representation.isIrreducible_iff_starAlgHom rho).2
      (isIrreducible_pureState_gnsStarAlgHom
        rootState rootState_mem_stateSpace isPureState_rootState)
  let pi : NonUnitalCStarRepresentation Limit f.GNS := rho.toNonUnitalStarAlgHom
  have hpi : pi.IsIrreducible := ⟨hrho.1, hrho.2⟩
  intro hGCR
  exact not_compact_le_range_nonunital pi hpi (hGCR.compact_le_range pi hpi)

/-- The fixed CAR completion also fails the independent internal condition,
using the proved internal-type-I-to-GCR implication. -/
theorem not_isInternalTypeI_limit : ¬ IsInternalTypeI Limit :=
  fun h => not_isGCR_limit h.isGCR

/-- An actual CAR quotient of a closed subalgebra obstructs GCR of the ambient
algebra. This consumes the exhibited subalgebra and surjection; existence of
such a subquotient is a separate construction. -/
theorem not_isGCR_of_subquotient {A : Type v} [NonUnitalCStarAlgebra A]
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] Limit) (hq : Function.Surjective q) : ¬ IsGCR A := by
  intro hA
  exact not_isGCR_limit ((hA.nonUnitalStarSubalgebra D).of_surjective q hq)

/-- The same exhibited CAR subquotient also contradicts the independent
internal condition, using only the already proved forward implication. -/
theorem not_isInternalTypeI_of_subquotient {A : Type v} [NonUnitalCStarAlgebra A]
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (q : D →⋆ₙₐ[ℂ] Limit) (hq : Function.Surjective q) : ¬ IsInternalTypeI A :=
  fun hA => not_isGCR_of_subquotient D q hq hA.isGCR

end MathlibAnnex.CStarAlgebra.CAR
