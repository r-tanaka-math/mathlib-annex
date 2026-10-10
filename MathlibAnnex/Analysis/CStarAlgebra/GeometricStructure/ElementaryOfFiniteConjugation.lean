/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.CompactIdealSeparation
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.CompactAnnihilatingRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.CompactModel
import Mathlib.Algebra.Star.StarAlgHom
import MathlibAnnex.Analysis.CStarAlgebra.CompactModelEquiv

/-!
# Compact-model endpoints and the singular-state contradiction

A received compact model has a genuine star-algebra equivalence onto the
existing compact subtype. This works for nonunital algebras; `StarAlgEquiv`
itself does not require a multiplicative unit. In finite Hilbert dimension,
the actual multiplier hypotheses prove such a compact model without any
quotient representation argument.

The earlier partial theorem is retained unchanged, including its conditional
finite-dimensional clause. The new singular-state construction proves the
reverse compact inclusion in arbitrary Hilbert dimension. The final endpoint
uses the SAME pure-state witness and literal preimage homeomorphism returned
by the multiplier argument. No new representation of the original singleton
algebra is selected for the compact model. The separating action is constructed
on its literal image solely to obtain a contradiction.

The compact algebra's singleton spectrum and the forward finite-conjugation
property remain independent obligations; this module does not redefine
`IsElementary` or assert the full equivalence in Paper 7.7.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section SingletonImage

variable [PartialOrder A] [StarOrderedRing A]
local instance (pi : NonUnitalCStarRepresentation A H) :
    NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- In the same faithful multiplier image, a noncompact member would produce
an actual compact-annihilating irreducible action on that image. Pullback to
the original singleton algebra contradicts its rank-one detection theorem. -/
theorem isCompactOperator_map_of_singleton_of_image_mul_mem
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi)) :
    ∀ a : A, IsCompactOperator (pi a) := by
  intro a
  by_contra ha
  let s : (NonUnitalStarAlgHom.range pi) := (NonUnitalStarAlgHom.rangeRestrict pi) a
  obtain ⟨psi, hpsi, hpure, hann, _hbound, hpos⟩ :=
    exists_pureState_annihilating_compacts_of_not_isCompactOperator
      (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)) s ha
  let f := positiveLinearMapOfMemStateSpace psi hpsi
  let rho : NonUnitalCStarRepresentation (NonUnitalStarAlgHom.range pi) f.GNS :=
    f.gnsStarAlgHom.toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ (NonUnitalStarAlgHom.range pi))
  have hprops : rho.IsIrreducible ∧ rho s ≠ 0 ∧
      ∀ c : (NonUnitalStarAlgHom.range pi), IsCompactOperator (c : H →L[ℂ] H) → rho c = 0 :=
    isIrreducible_restriction_gns_of_pureState_annihilating
      (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range pi)) s psi hpsi hpure hann hpos
  exact (not_isIrreducible_of_image_annihilates_compacts
    hsingle pi hpi hinj hmul rho hprops.2.2) hprops.1

/-- No finite-dimensional or separability hypothesis is needed once the
same faithful image absorbs all bounded multipliers and has singleton spectrum. -/
theorem isCompactOperatorModel_of_singleton_of_image_mul_mem
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi)) :
    IsCompactOperatorModel pi := by
  exact ⟨hinj, isCompactOperator_map_of_singleton_of_image_mul_mem
    hsingle pi hpi hinj hmul,
    exists_preimage_compact_of_image_mul_mem pi hinj hpi.1 hmul⟩

/-- Literal range equality, not merely abstract isomorphism of the algebras. -/
theorem range_eq_compactOperatorStarSubalgebra_of_singleton_of_image_mul_mem
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (hinj : Function.Injective pi)
    (hmul : ∀ (b a : H →L[ℂ] H), a ∈ (NonUnitalStarAlgHom.range pi) →
      b * a ∈ (NonUnitalStarAlgHom.range pi) ∧ a * b ∈ (NonUnitalStarAlgHom.range pi)) :
    (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H := by
  have hmodel := isCompactOperatorModel_of_singleton_of_image_mul_mem
    hsingle pi hpi hinj hmul
  ext T
  constructor
  · intro hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hT
    exact hmodel.2.1 a
  · intro hT
    exact (NonUnitalStarAlgHom.mem_range pi).2 (hmodel.2.2 T hT)

end SingletonImage

section OriginalAlgebra

variable [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
local instance (pi : NonUnitalCStarRepresentation A H) :
    NonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (NonUnitalStarAlgHom.range pi)
    (h_closed := HomKernelQuotient.isClosed_image pi)

/-- Joint partial endpoint for the original algebra. The pure state, faithful
representation and literal preimage map are unchanged. A separating irreducible
image action is ruled out, but its existence from properness is NOT presumed.
The finite-dimensional implication closes exactly that independent branch. -/
theorem exists_faithful_image_compact_obstruction_of_singleton
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (hproperty : ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{u, max u w})) :
    ∃ phi : NonUnitalPureState A,
      Function.Injective phi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ ∧
      ∃ r : ClosureSpace.Homeomorph
          ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
            (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))
          (NormedSpace.geometricStructureClosure ℂ A),
        (∀ J : normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation),
          (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val.val) ∧
        (∀ T : phi.GNS →L[ℂ] phi.GNS, IsCompactOperator T →
          ∃ a : A, phi.gnsRepresentation a = T) ∧
        (FiniteDimensional ℂ phi.GNS → IsCompactOperatorModel phi.gnsRepresentation) ∧
        (∀ (K : Type z) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
          (rho : NonUnitalCStarRepresentation (NonUnitalStarAlgHom.range phi.gnsRepresentation) K),
          (∀ a : (NonUnitalStarAlgHom.range phi.gnsRepresentation),
            IsCompactOperator (a : phi.GNS →L[ℂ] phi.GNS) → rho a = 0) →
          ¬ rho.IsIrreducible) := by
  obtain ⟨phi, hfaith, hnormal, r, hr, _I, _hcarrier, _hI, _hclosed, _hcomp,
      hmul, hpre⟩ := exists_faithful_image_operatorIdeal_of_singleton.{u, w} hsingle hproperty
  refine ⟨phi, hfaith, hnormal, r, hr, hpre, ?_, ?_⟩
  · intro hfinite
    letI := hfinite
    exact isCompactOperatorModel_of_finiteDimensional_of_image_mul_mem
      phi.gnsRepresentation hfaith phi.isIrreducible_gnsRepresentation.1 hmul
  · intro K _ _ _ rho hann
    exact not_isIrreducible_of_image_annihilates_compacts
      hsingle phi.gnsRepresentation phi.isIrreducible_gnsRepresentation hfaith hmul rho hann

/-- The reverse finite-conjugation implication reaches the compact model of
the original algebra. The same `phi`, `pi`, image, and preimage homeomorphism
are retained. The displayed star equivalence and its inverse use this `pi`.
This does not assert the converse compact-algebra test property. -/
theorem exists_faithful_compactOperatorModel_of_singleton_finiteConjugation
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (hproperty : ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{u, max u w})) :
    ∃ phi : NonUnitalPureState A,
      Function.Injective phi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ ∧
      ∃ r : ClosureSpace.Homeomorph
          ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
            (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))
          (NormedSpace.geometricStructureClosure ℂ A),
        (∀ J : normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation),
          (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val.val) ∧
        ∃ hmodel : IsCompactOperatorModel phi.gnsRepresentation,
          (NonUnitalStarAlgHom.range phi.gnsRepresentation) =
            ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ∧
          (∀ a : A, (compactOperatorStarAlgEquiv phi.gnsRepresentation hmodel a).val =
            phi.gnsRepresentation a) ∧
          (∀ T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS,
            phi.gnsRepresentation ((compactOperatorStarAlgEquiv
              phi.gnsRepresentation hmodel).symm T) = T.val) ∧
          ∀ a : A, ‖compactOperatorStarAlgEquiv phi.gnsRepresentation hmodel a‖ = ‖a‖ := by
  obtain ⟨phi, hfaith, hnormal, r, hr, _I, _hcarrier, _hI, _hclosed, _hcomp,
      hmul, _hpre⟩ := exists_faithful_image_operatorIdeal_of_singleton.{u, w} hsingle hproperty
  have hmodel := isCompactOperatorModel_of_singleton_of_image_mul_mem
    hsingle phi.gnsRepresentation phi.isIrreducible_gnsRepresentation hfaith hmul
  refine ⟨phi, hfaith, hnormal, r, hr, hmodel, ?_, ?_, ?_, ?_⟩
  · exact range_eq_compactOperatorStarSubalgebra_of_singleton_of_image_mul_mem
      hsingle phi.gnsRepresentation phi.isIrreducible_gnsRepresentation hfaith hmul
  · exact compactOperatorStarAlgEquiv_apply phi.gnsRepresentation hmodel
  · exact compactOperatorStarAlgEquiv_symm_apply phi.gnsRepresentation hmodel
  · exact norm_compactOperatorStarAlgEquiv_apply phi.gnsRepresentation hmodel

end OriginalAlgebra
end MathlibAnnex.Analysis.CStarAlgebra
