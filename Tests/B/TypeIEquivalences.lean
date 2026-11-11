/-
New typed consumers; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import MathlibAnnex.Analysis.CStarAlgebra.TypeI.Equivalences

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

-- These final scopes contain no supplied positive map, separability,
-- unit, nontriviality, normality, or existence-of-test-representation input.
example (hA : IsTypeIBidual A) : IsInternalTypeI A :=
  hA.isInternalTypeI

example (hA : IsInternalTypeI A) : IsTypeIBidual A :=
  hA.isTypeIBidual

example (hA : IsTypeIBidual A) : IsGCR A :=
  hA.isGCR

example (hA : IsGCR A) : IsTypeIBidual A :=
  hA.isTypeIBidual

example : IsInternalTypeI A ↔ IsTypeIBidual A :=
  isInternalTypeI_iff_isTypeIBidual

example : IsTypeIBidual A ↔ IsGCR A :=
  isTypeIBidual_iff_isGCR

-- All three pairwise equivalences use the existing distinct predicates.
example :
    (IsInternalTypeI A ↔ IsTypeIBidual A) ∧
    (IsTypeIBidual A ↔ IsGCR A) ∧
    (IsInternalTypeI A ↔ IsGCR A) :=
  ⟨isInternalTypeI_iff_isTypeIBidual, isTypeIBidual_iff_isGCR,
    isInternalTypeI_iff_isGCR⟩

-- The zero algebra stays in the final scope, with no nonzero test vector.
example [Subsingleton A] :
    IsInternalTypeI A ∧ IsTypeIBidual A ∧ IsGCR A := by
  have hi : IsInternalTypeI A := isInternalTypeI_of_subsingleton
  have hb : IsTypeIBidual A := hi.isTypeIBidual
  exact ⟨hb.isInternalTypeI, hb, hb.isGCR⟩

-- A direct consumer of the raw double strong dual uses the old Arens
-- multiplication and involution. No second product or carrier is introduced.
example :
    IsInternalTypeI A ↔
      ∀ P : StrongDual ℂ (StrongDual ℂ A),
        arensProduct P P = P → bidualStar P = P → P ≠ 0 →
        ∃ Q : StrongDual ℂ (StrongDual ℂ A),
          arensProduct Q Q = Q ∧ bidualStar Q = Q ∧ Q ≠ 0 ∧
          arensProduct Q P = Q ∧
          ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
            arensProduct Q X = X → arensProduct X Q = X →
            arensProduct Q Y = Y → arensProduct Y Q = Y →
            arensProduct X Y = arensProduct Y X :=
  isInternalTypeI_iff_isTypeIBidual.trans isTypeIBidual_iff_arensProduct

-- This checks the same literal-bidual criterion in the reverse direction.
example
    (hraw : ∀ P : StrongDual ℂ (StrongDual ℂ A),
      arensProduct P P = P → bidualStar P = P → P ≠ 0 →
      ∃ Q : StrongDual ℂ (StrongDual ℂ A),
        arensProduct Q Q = Q ∧ bidualStar Q = Q ∧ Q ≠ 0 ∧
        arensProduct Q P = Q ∧
        ∀ X Y : StrongDual ℂ (StrongDual ℂ A),
          arensProduct Q X = X → arensProduct X Q = X →
          arensProduct Q Y = Y → arensProduct Y Q = Y →
          arensProduct X Y = arensProduct Y X) : IsGCR A :=
  (isTypeIBidual_iff_arensProduct.mpr hraw).isGCR

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

-- Nontriviality appears only for the actual obstruction construction.
-- The concrete CAR map and both of its identities are already discharged.
example [Nontrivial A] (hA : IsAntiliminal A) :
    ∃ (phi : Unitization ℂ A →L[ℂ] ℂ)
        (hphi : phi ∈ stateSpace (Unitization ℂ A)),
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor ∧
      ¬ (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsTypeI :=
  hA.exists_factor_state_not_isTypeI
