/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Typed consumers of the production results.
-/

import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Sakai

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {Q : Type w} [NonUnitalCStarAlgebra Q]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (pi : NonUnitalCStarRepresentation A H)
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    pi.IsNonzero :=
  isNonzero_of_not_isTypeI_generated pi hnotI

example (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    pi.IsNondegenerate :=
  isNondegenerate_of_isFactor_of_not_isTypeI pi hfactor hnotI

example (rho : Representation (Unitization ℂ Q) H)
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    NonUnitalCStarRepresentation.IsNonzero (Unitization.starLift.symm rho : NonUnitalCStarRepresentation Q H) :=
  isNonzero_restriction_of_not_isTypeI rho hnotI

example (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    let pi : NonUnitalCStarRepresentation Q H := Unitization.starLift.symm rho
    pi.IsNonzero ∧ pi.IsNondegenerate ∧ pi.unitization = rho := by
  exact ⟨isNonzero_restriction_of_not_isTypeI rho hnotI,
    isNondegenerate_restriction_of_not_isTypeI rho hfactor hnotI,
    Unitization.starLift.apply_symm_apply rho⟩

example (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated pi.unitization.range) ∧
      (¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) ∧
      ∀ a : A, pi a = rho (Unitization.inr (q a)) := by
  obtain ⟨hnz, hnd, hgen, hdiag⟩ :=
    restriction_comp_spec_of_not_isTypeI q hq rho hfactor hnotI
  refine ⟨hnz, hnd, ?_, ?_, hdiag⟩
  · rw [hgen]
    exact hfactor
  · rw [hgen]
    exact hnotI

set_option maxHeartbeats 800000 in
example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    let pi : NonUnitalCStarRepresentation A H :=
      (Unitization.starLift.symm rho).comp (ClosedIdealQuotient.mkHom J hJ)
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      (∀ a : A, pi a = rho (Unitization.inr (ClosedIdealQuotient.mkHom J hJ a))) ∧
      ∀ a : A, a ∈ J → pi a = 0 := by
  obtain ⟨hnz, hnd, hgen, hdiag⟩ :=
    restriction_mkHom_spec_of_not_isTypeI J hJ rho hfactor hnotI
  refine ⟨hnz, hnd, hgen, hdiag, ?_⟩
  intro a ha
  exact (congrArg (Unitization.starLift.symm rho)
    ((ClosedIdealQuotient.mkHom_eq_zero_iff J hJ a).mpr ha)).trans (map_zero _)

example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (hnotI : ¬ (VonNeumannAlgebra.generated pi.unitization.range).IsTypeI) :
    ¬ IsTypeIBidual A :=
  not_isTypeIBidual_of_not_isTypeI_generated pi hnd hnotI

example (hA : IsGCR A) : IsTypeIBidual A :=
  hA.isTypeIBidual

example (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    ¬ IsTypeIBidual A :=
  not_isTypeIBidual_of_not_isTypeI_quotient q hq rho hfactor hnotI

set_option maxHeartbeats 800000 in
example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    ¬ IsTypeIBidual A :=
  not_isTypeIBidual_of_not_isTypeI_quotient (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hnotI

example (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hnotI : ¬ (VonNeumannAlgebra.generated rho.range).IsTypeI) :
    ¬ IsGCR A := by
  intro hA
  exact not_isTypeIBidual_of_not_isTypeI_quotient q hq rho hfactor hnotI hA.isTypeIBidual
