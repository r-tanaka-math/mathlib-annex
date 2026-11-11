/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.FactorRestriction
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRConverse

/-!
# Non-type-I factor tests for the literal bidual

A representation of the unitization whose generated algebra is not type I
cannot vanish on the original algebra: its vanishing would make the same
generated algebra commutative. The factor condition then forces the actual
original-algebra action to be nondegenerate, by the existing essential
projection dichotomy. No replacement of the represented Hilbert space occurs.

The existing surjective-composition and closed-ideal quotient constructions
give an exact diagram on original elements and equality of the concrete
generated algebras. The actual normal enveloping quotient then rules out
type I of the original literal Banach bidual.

These lemmas do not assert that a supplied factor is non-type-I. That
construction is a separate part of the diffuse test argument. In particular,
the final reverse Sakai theorem and the three-way equivalence are not
declared here with their missing construction as an additional hypothesis.
The source algebra and quotient may be nonunital, nonseparable, or zero;
their universes and the represented Hilbert universe remain independent.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {Q : Type w} [NonUnitalCStarAlgebra Q]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace NonUnitalCStarRepresentation

/-- A zero original-algebra action would have a commutative generated
unitization algebra, hence type I. No factor hypothesis is needed here. -/
theorem isNonzero_of_not_isTypeI_generated
    (pi : NonUnitalCStarRepresentation A H)
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    pi.IsNonzero := by
  classical
  by_contra hnz
  have hzero : ∀ a : A, pi a = 0 := by
    intro a
    by_contra ha
    exact hnz ⟨a, ha⟩
  let M := VonNeumannAlgebra.generated pi.unitization.range
  have hc (T : H →L[ℂ] H) : T ∈ Set.centralizer (Set.range pi.unitization) := by
    rw [centralizer_range_unitization]
    rintro _ ⟨a, rfl⟩
    simp only [hzero a, zero_mul, mul_zero]
  have hcomm : ∀ S T : M.toStarSubalgebra, S * T = T * S := by
    intro S T
    apply Subtype.ext
    exact ((VonNeumannAlgebra.mem_generated_iff pi.unitization.range
      (S : H →L[ℂ] H)).mp S.property (T : H →L[ℂ] H) (hc T)).symm
  exact hnotI (VonNeumannAlgebra.isTypeI_of_commutative M hcomm)

/-- The same original action is nondegenerate once its generated
unitization algebra is a non-type-I factor. -/
theorem isNondegenerate_of_isFactor_of_not_isTypeI
    (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    pi.IsNondegenerate :=
  isNondegenerate_of_isFactor_of_isNonzero pi hfactor
    (isNonzero_of_not_isTypeI_generated pi hnotI)

/-- The inverse of Mathlib's unitization universal property is the actual
nonzero restriction of any non-type-I generated representation. -/
theorem isNonzero_restriction_of_not_isTypeI
    (rho : Representation (Unitization ℂ A) H)
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    NonUnitalCStarRepresentation.IsNonzero (Unitization.starLift.symm rho : NonUnitalCStarRepresentation A H) := by
  apply isNonzero_of_not_isTypeI_generated
  simpa only [unitization, Equiv.apply_symm_apply] using hnotI

/-- The canonical restriction of a non-type-I factor representation acts
nondegenerately on its original Hilbert space. -/
theorem isNondegenerate_restriction_of_not_isTypeI
    (rho : Representation (Unitization ℂ A) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    NonUnitalCStarRepresentation.IsNondegenerate (Unitization.starLift.symm rho : NonUnitalCStarRepresentation A H) := by
  apply isNondegenerate_of_isFactor_of_not_isTypeI
  · simpa only [unitization, Equiv.apply_symm_apply] using hfactor
  · simpa only [unitization, Equiv.apply_symm_apply] using hnotI

/-- Surjective pullback preserves the actual represented range, while
nonzeroness and nondegeneracy are derived from the given non-type-I factor. -/
theorem restriction_comp_spec_of_not_isTypeI
    (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      ∀ a : A, pi a = rho (Unitization.inr (q a)) := by
  dsimp only
  refine ⟨(isNonzero_comp_iff_of_surjective _ q hq).mpr
      (isNonzero_restriction_of_not_isTypeI rho hnotI),
    (isNondegenerate_comp_iff_of_surjective _ q hq).mpr
      (isNondegenerate_restriction_of_not_isTypeI rho hfactor hnotI), ?_, fun _ => rfl⟩
  simpa only [unitization, Equiv.apply_symm_apply] using
    generated_unitization_comp_of_surjective
      (Unitization.starLift.symm rho : NonUnitalCStarRepresentation Q H) q hq

/-- The diagram for the existing Banach quotient by an arbitrary closed
two-sided ideal. Properness is not assumed separately; a non-type-I factor
already supplies the necessary nonzero action. -/
theorem restriction_mkHom_spec_of_not_isTypeI
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    let pi : NonUnitalCStarRepresentation A H :=
      (Unitization.starLift.symm rho).comp (ClosedIdealQuotient.mkHom J hJ)
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      ∀ a : A, pi a = rho (Unitization.inr (ClosedIdealQuotient.mkHom J hJ a)) :=
  restriction_comp_spec_of_not_isTypeI (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hnotI

end NonUnitalCStarRepresentation

/-- The supplied CAR-subquotient proof of GCR implies internal type I is
independent of bidual classification. Composing it with the established
forward implication gives type I of the literal bidual without a cycle. -/
theorem IsGCR.isTypeIBidual (hA : IsGCR A) : IsTypeIBidual A :=
  hA.isInternalTypeI.isTypeIBidual

/-- A non-type-I generated image of a genuine nondegenerate action
contradicts the established type I transport from the literal bidual. -/
theorem not_isTypeIBidual_of_not_isTypeI_generated
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    ¬ IsTypeIBidual A := by
  intro hA
  exact hnotI (hA.isTypeI_generated pi hnd)

/-- A non-type-I factor representation of the unitization of an actual
surjective quotient obstructs type I of the original literal Banach bidual.
The nondegenerate original-algebra action is proved, not a supplied premise. -/
theorem not_isTypeIBidual_of_not_isTypeI_quotient
    (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    ¬ IsTypeIBidual A := by
  let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
  obtain ⟨_hnz, hnd, hgen, _hdiag⟩ :=
    NonUnitalCStarRepresentation.restriction_comp_spec_of_not_isTypeI q hq rho hfactor hnotI
  apply not_isTypeIBidual_of_not_isTypeI_generated pi hnd
  rw [hgen]
  exact hnotI

end MathlibAnnex.Analysis.CStarAlgebra
