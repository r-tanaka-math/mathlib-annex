/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.CompactModelEquiv
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactRepresentationCharacterization

/-!
# Faithful compact representations from exact elementary models

The representation is the concrete compact-operator inclusion composed with
an explicitly supplied star equivalence. No new elementary or compactness
predicate is introduced. Repackaging an existing exact representation with
`compactOperatorStarAlgEquiv` and then applying the construction returns the
same representation, not another witness chosen from an existence theorem.

The target Hilbert universe is independent of the algebra universe. No
nontriviality of the algebra or the Hilbert space is required, so a zero
compact-operator model remains allowed. The conclusion about the canonical
reduced atomic representation uses the existing pointwise characterization;
it does not identify that representation with the elementary representation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- The actual compact-operator inclusion composed with the specified exact
model. This construction does not choose a new elementary model. -/
def ofCompactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    NonUnitalCStarRepresentation A H :=
  (NonUnitalStarSubalgebraClass.subtype
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)).comp
      E.toNonUnitalStarAlgHom

@[simp]
theorem ofCompactOperatorEquiv_apply
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (a : A) :
    ofCompactOperatorEquiv E a = (E a).val := rfl

/-- Faithfulness is inherited from the given equivalence and the actual
subtype inclusion, also for the zero algebra. -/
theorem ofCompactOperatorEquiv_injective
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    Function.Injective (ofCompactOperatorEquiv E) := by
  intro a b hab
  apply E.injective
  apply Subtype.ext
  exact hab

/-- The same composite is an exact model: every compact operator has its
specified preimage under `E.symm`. -/
theorem isCompactOperatorModel_ofCompactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    IsCompactOperatorModel (ofCompactOperatorEquiv E) := by
  refine ⟨ofCompactOperatorEquiv_injective E, fun a => (E a).property, ?_⟩
  intro T hT
  refine ⟨E.symm ⟨T, hT⟩, ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply ⟨T, hT⟩)

/-- The existing faithful compact-valued predicate holds for the same map. -/
theorem isCompactlyRepresented_ofCompactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    (ofCompactOperatorEquiv E).IsCompactlyRepresented :=
  ⟨ofCompactOperatorEquiv_injective E, fun a => (E a).property⟩

@[simp]
theorem norm_ofCompactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (a : A) :
    ‖ofCompactOperatorEquiv E a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (ofCompactOperatorEquiv E)
    (ofCompactOperatorEquiv_injective E) a

/-- Isometry concerns the concrete inclusion composite, not an unspecified
representation whose existence follows from the model. -/
theorem isometry_ofCompactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    Isometry (ofCompactOperatorEquiv E) :=
  NonUnitalStarAlgHom.isometry (ofCompactOperatorEquiv E)
    (ofCompactOperatorEquiv_injective E)

/-- Repackaging and then including an existing exact compact model preserves
its actual action as a bundled representation. -/
@[simp]
theorem ofCompactOperatorEquiv_compactOperatorStarAlgEquiv
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    ofCompactOperatorEquiv (compactOperatorStarAlgEquiv pi hpi) = pi := by
  ext a
  rfl

end NonUnitalCStarRepresentation

namespace PrimitiveSpectrum

/-- An exact elementary model on any independently specified Hilbert universe
makes the pre-existing canonical reduced atomic representation compact. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_compactOperatorEquiv
    (E : A ≃⋆ₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented :=
  isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactlyRepresented
    (NonUnitalCStarRepresentation.ofCompactOperatorEquiv E)
    (NonUnitalCStarRepresentation.isCompactlyRepresented_ofCompactOperatorEquiv E)

/-- The given-representation formulation reuses an existing exact model
without defining a second action or excluding a zero Hilbert model. -/
theorem isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactOperatorModel
    (pi : NonUnitalCStarRepresentation A H) (hpi : IsCompactOperatorModel pi) :
    (reducedAtomicRepresentation (A := A)).IsCompactlyRepresented :=
  isCompactlyRepresented_reducedAtomicRepresentation_of_isCompactlyRepresented
    pi ⟨hpi.1, hpi.2.1⟩

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra

end
