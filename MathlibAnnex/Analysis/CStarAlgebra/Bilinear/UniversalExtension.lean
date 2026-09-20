import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.UniversalRowColumn
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.TensorExtension

/-!
# Unconditional C*-bilinear weak compactness and canonical extension

The analytic input is proved in `UniversalRowColumn`, not a parameter here.
The genuinely nonunital case uses the existing concrete two-sided unitization
extension and descends through its actual inclusions.  No bidual multiplication
or order instance is introduced by this file.  The chosen extension is always
`firstArens` of the original form, including after unitization descent.

SOURCE_UNBUILT: written proof bodies; no local Lean validation is reported.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.BidualBilinear
open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.WeakCompact

universe uA uD

section Unital

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- W1 for every bounded form on two unital C*-algebras, including zero
algebras. The constant is fixed by the form, not by a finite family. -/
theorem isWeaklyCompact_unital (B : A →L[ℂ] D →L[ℂ] ℂ) :
    IsWeaklyCompact B := by
  obtain ⟨C, hC, hrow⟩ := exists_rowColumnEstimate B
  exact isWeaklyCompact_of_rowColumn_total B C hC hrow

/-- W2 for the canonical first extension of an arbitrary unital form. -/
theorem bilinear_extension_data_unital (B : A →L[ℂ] D →L[ℂ] ℂ) :
    SeparatelyWeakStarContinuous (firstArens B) ∧
      Extends B (firstArens B) ∧ ‖firstArens B‖ = ‖B‖ :=
  ⟨separatelyWeakStarContinuous_firstArens B (isWeaklyCompact_unital B),
    firstArens_canonical B, norm_firstArens B⟩

/-- Every unital projective-tensor dual, not a selected elementary tensor or
an evaluation functional, has the norm-preserving canonical W2 extension. -/
theorem tensor_extension_data_unital (f : StrongDual ℂ (Completion ℂ A D)) :
    SeparatelyWeakStarContinuous (firstArens (tensorDualIsometry f)) ∧
      Extends (tensorDualIsometry f) (firstArens (tensorDualIsometry f)) ∧
      ‖firstArens (tensorDualIsometry f)‖ = ‖f‖ := by
  obtain ⟨C, hC, hrow⟩ := exists_rowColumnEstimate (tensorDualIsometry f)
  exact tensor_extension_data_of_rowColumn f C hC hrow

/-- The two initially one-sided constructions agree as tensor functionals. -/
theorem tensor_extensions_eq_unital (f : StrongDual ℂ (Completion ℂ A D)) :
    firstExtensionFunctional f = secondExtensionFunctional f :=
  (isArensRegular_iff_tensor_extensions_eq f).mp
    (isWeaklyCompact_unital (tensorDualIsometry f))

end Unital

section Nonunital

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {D : Type uD} [NonUnitalCStarAlgebra D]

/-- W1 for genuinely nonunital algebras. The retained coordinate projections
need only be bounded; no assertion that they are contractive is made. -/
theorem isWeaklyCompact_nonunital (B : A →L[ℂ] D →L[ℂ] ℂ) :
    IsWeaklyCompact B := by
  obtain ⟨C, hC, hrow⟩ := exists_rowColumnEstimate (twoSidedUnitizationExtension B)
  exact isWeaklyCompact_of_unitizedRowColumn B C hC hrow

/-- Equality of the first and second extensions is derived from W1; it is
not an input to the normalized analytic estimate. -/
theorem firstArens_eq_secondArens_nonunital (B : A →L[ℂ] D →L[ℂ] ℂ) :
    firstArens B = secondArens B :=
  (isWeaklyCompact_iff_firstArens_eq_secondArens B).mp
    (isWeaklyCompact_nonunital B)

/-- Canonical bilinear W2 on the original nonunital algebras' biduals. -/
theorem bilinear_extension_data_nonunital (B : A →L[ℂ] D →L[ℂ] ℂ) :
    SeparatelyWeakStarContinuous (firstArens B) ∧
      Extends B (firstArens B) ∧ ‖firstArens B‖ = ‖B‖ :=
  ⟨separatelyWeakStarContinuous_firstArens B (isWeaklyCompact_nonunital B),
    firstArens_canonical B, norm_firstArens B⟩

/-- Canonical W2 for every projective-tensor dual on independent nonunital
carriers. Unitization is an internal proof step, not an added hypothesis. -/
theorem tensor_extension_data_nonunital (f : StrongDual ℂ (Completion ℂ A D)) :
    SeparatelyWeakStarContinuous (firstArens (tensorDualIsometry f)) ∧
      Extends (tensorDualIsometry f) (firstArens (tensorDualIsometry f)) ∧
      ‖firstArens (tensorDualIsometry f)‖ = ‖f‖ := by
  obtain ⟨C, hC, hrow⟩ :=
    exists_rowColumnEstimate (twoSidedUnitizationExtension (tensorDualIsometry f))
  exact tensor_extension_data_of_unitizedRowColumn f C hC hrow

/-- In particular the two canonical tensor extension functionals coincide. -/
theorem tensor_extensions_eq_nonunital (f : StrongDual ℂ (Completion ℂ A D)) :
    firstExtensionFunctional f = secondExtensionFunctional f :=
  (isArensRegular_iff_tensor_extensions_eq f).mp
    (isWeaklyCompact_nonunital (tensorDualIsometry f))

end Nonunital

end MathlibAnnex.CStarBilinear
