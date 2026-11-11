import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.FactorRestriction

/-!
Typed restriction and actual-quotient consumers. The final consumer feeds
the produced nonzero nondegenerate action into the independently proved
literal-bidual obstruction. No type III representation is postulated by a
new class or axiom. Its existence is a separate mathematical obligation.
This consumer is checked on the submitted representation and the actual quotient map.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.FactorRestrictionConsumers

open NonUnitalCStarRepresentation

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {Q : Type w} [NonUnitalCStarAlgebra Q]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (pi : NonUnitalCStarRepresentation Q H) (q : A →⋆ₙₐ[ℂ] Q)
    (hq : Function.Surjective q) :
    unitization (pi.comp q) = pi.unitization.comp (Unitization.starMap q) ∧
      (unitization (pi.comp q)).range = pi.unitization.range ∧
      VonNeumannAlgebra.generated (unitization (pi.comp q)).range =
        VonNeumannAlgebra.generated pi.unitization.range :=
  ⟨unitization_comp pi q, unitization_range_comp_of_surjective pi q hq,
    generated_unitization_comp_of_surjective pi q hq⟩

example (pi : NonUnitalCStarRepresentation Q H) (q : A →⋆ₙₐ[ℂ] Q)
    (hq : Function.Surjective q) :
    (IsNonzero (pi.comp q) ↔ pi.IsNonzero) ∧
      (IsNondegenerate (pi.comp q) ↔ pi.IsNondegenerate) :=
  ⟨isNonzero_comp_iff_of_surjective pi q hq,
    isNondegenerate_comp_iff_of_surjective pi q hq⟩

example (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range)) :
    pi.essentialProjection = 0 ∨ pi.essentialProjection = 1 :=
  essentialProjection_eq_zero_or_eq_one_of_isFactor pi hfactor

example (pi : NonUnitalCStarRepresentation A H)
    (hfactor : VonNeumannAlgebra.IsFactor
      (VonNeumannAlgebra.generated pi.unitization.range)) (hnz : pi.IsNonzero) :
    pi.IsNondegenerate :=
  isNondegenerate_of_isFactor_of_isNonzero pi hfactor hnz

/-- The original restriction is used; it is not replaced by a separately
chosen representation on its essential subspace. -/
example (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    let pi : NonUnitalCStarRepresentation Q H := Unitization.starLift.symm rho
    pi.IsNonzero ∧ pi.IsNondegenerate ∧ pi.unitization = rho := by
  exact ⟨isNonzero_restriction_of_isTypeIII rho hfactor hIII,
    isNondegenerate_restriction_of_isTypeIII rho hfactor hIII,
    Unitization.starLift.apply_symm_apply rho⟩

example (q : A →⋆ₙₐ[ℂ] Q) (hq : Function.Surjective q)
    (rho : Representation (Unitization ℂ Q) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    let pi : NonUnitalCStarRepresentation A H := (Unitization.starLift.symm rho).comp q
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated pi.unitization.range) ∧
      (VonNeumannAlgebra.generated pi.unitization.range).IsTypeIII ∧
      ∀ a : A, pi a = rho (Unitization.inr (q a)) := by
  obtain ⟨hnz, hnd, hgen, hdiag⟩ := restriction_comp_spec q hq rho hfactor hIII
  refine ⟨hnz, hnd, ?_, ?_, hdiag⟩
  · rw [hgen]
    exact hfactor
  · rw [hgen]
    exact hIII

/-- The actual quotient map annihilates the stated ideal in the composed
action, while the same generated algebra and the explicit diagram remain. -/
example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    let pi : NonUnitalCStarRepresentation A H :=
      (Unitization.starLift.symm rho).comp (ClosedIdealQuotient.mkHom J hJ)
    pi.IsNonzero ∧ pi.IsNondegenerate ∧
      VonNeumannAlgebra.generated pi.unitization.range =
        VonNeumannAlgebra.generated rho.range ∧
      (∀ a : A, pi a = rho (Unitization.inr (ClosedIdealQuotient.mkHom J hJ a))) ∧
      ∀ a : A, a ∈ J → pi a = 0 := by
  obtain ⟨hnz, hnd, hgen, hdiag⟩ := restriction_mkHom_spec J hJ rho hfactor hIII
  refine ⟨hnz, hnd, hgen, hdiag, ?_⟩
  intro a ha
  change (Unitization.starLift.symm rho :
    NonUnitalCStarRepresentation (ClosedIdealQuotient.Quotient J hJ) H)
      (ClosedIdealQuotient.mkHom J hJ a) = 0
  rw [(ClosedIdealQuotient.mkHom_eq_zero_iff J hJ a).mpr ha, map_zero]

/-- The independently constructed type III image obstruction consumes
the proved original-algebra action and applies to the literal bidual. -/
example (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (rho : Representation (Unitization ℂ (ClosedIdealQuotient.Quotient J hJ)) H)
    (hfactor : VonNeumannAlgebra.IsFactor (VonNeumannAlgebra.generated rho.range))
    (hIII : (VonNeumannAlgebra.generated rho.range).IsTypeIII) :
    ¬ IsTypeIBidual A :=
  not_isTypeIBidual_of_isTypeIII_quotient (ClosedIdealQuotient.mkHom J hJ)
    (ClosedIdealQuotient.mkHom_surjective J hJ) rho hfactor hIII

end MathlibAnnex.Analysis.CStarAlgebra.FactorRestrictionConsumers
