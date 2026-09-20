import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.NormalExtension
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.RowColumnSeparation
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.TensorDual
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Unitization

/-!
# Canonical tensor extensions from row/column estimates

This generic library module contains the reusable providers first exercised in
`BIL3Use.lean`.  It keeps the analytic row/column premise explicit, handles
independent carrier universes, and performs the two-sided unitization descent
without adding a second bidual algebra structure.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.BidualBilinear
open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.WeakCompact

universe uA uD

noncomputable section

section Unital

variable {A : Type uA} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- For arbitrary unital algebras, the sole remaining analytic row/column
estimate supplies canonical Arens-extension data for every tensor-dual
functional.  The total weak-compactness consumer handles zero algebras
without asking for a normalized state. -/
theorem tensor_extension_data_of_rowColumn
    (f : StrongDual ℂ (Completion ℂ A D)) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate (tensorDualIsometry f) C) :
    SeparatelyWeakStarContinuous
        (firstArens (tensorDualIsometry f)) ∧
      Extends (tensorDualIsometry f)
        (firstArens (tensorDualIsometry f)) ∧
      ‖firstArens (tensorDualIsometry f)‖ = ‖f‖ := by
  have hf : IsArensRegular f :=
    isWeaklyCompact_of_rowColumn_total
      (tensorDualIsometry f) C hC hrow
  refine ⟨separatelyWeakStarContinuous_firstExtension f hf,
    firstArens_canonical _, ?_⟩
  simpa only [norm_firstArens] using
    (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := D)).norm_map f

/-- Under the same explicit analytic supplier, the two canonical tensor
extensions of an arbitrary `f` agree. -/
theorem tensor_extensions_eq_of_rowColumn
    (f : StrongDual ℂ (Completion ℂ A D)) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate (tensorDualIsometry f) C) :
    firstExtensionFunctional f = secondExtensionFunctional f :=
  (isArensRegular_iff_tensor_extensions_eq f).mp
    (isWeaklyCompact_of_rowColumn_total
      (tensorDualIsometry f) C hC hrow)

end Unital

section TwoSidedUnitization

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {D : Type uD} [NonUnitalCStarAlgebra D]

/-- Extend a form on two possibly different nonunital C-star algebras to
their independent minimal unitizations. -/
def twoSidedUnitizationExtension (B : A →L[ℂ] D →L[ℂ] ℂ) :
    Unitization ℂ A →L[ℂ] Unitization ℂ D →L[ℂ] ℂ :=
  precompRight
    (B.comp (unitizationProjection (A := A)))
    (unitizationProjection (A := D))

@[simp]
theorem twoSidedUnitizationExtension_apply
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (x : Unitization ℂ A) (y : Unitization ℂ D) :
    twoSidedUnitizationExtension B x y = B x.snd y.snd := rfl

@[simp]
theorem twoSidedUnitizationExtension_inclusion
    (B : A →L[ℂ] D →L[ℂ] ℂ) (x : A) (y : D) :
    twoSidedUnitizationExtension B
      (unitizationInclusion x) (unitizationInclusion y) = B x y := by
  simp [twoSidedUnitizationExtension]

/-- Weak compactness descends from the two-sided unitization extension.
This keeps the two carrier universes independent. -/
theorem isWeaklyCompact_of_twoSidedUnitizationExtension
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (hB : IsWeaklyCompact (twoSidedUnitizationExtension B)) :
    IsWeaklyCompact B := by
  have hpre : IsWeaklyCompact
      ((twoSidedUnitizationExtension B).comp
        (unitizationInclusion (A := A))) :=
    isWeaklyCompact_precomp (twoSidedUnitizationExtension B) hB
      (unitizationInclusion (A := A))
  have hpost : IsWeaklyCompact
      ((restrictUnitizationDual (A := D)).comp
        ((twoSidedUnitizationExtension B).comp
          (unitizationInclusion (A := A)))) :=
    isWeaklyCompact_postcomp
      ((twoSidedUnitizationExtension B).comp
        (unitizationInclusion (A := A))) hpre
      (restrictUnitizationDual (A := D))
  have heq : (restrictUnitizationDual (A := D)).comp
      ((twoSidedUnitizationExtension B).comp
        (unitizationInclusion (A := A))) = B := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp [restrictUnitizationDual]
  rwa [heq] at hpost

/-- A state-free row/column estimate on the concrete two-sided unitization
therefore supplies weak compactness of the original genuinely nonunital
form. -/
theorem isWeaklyCompact_of_unitizedRowColumn
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate
      (twoSidedUnitizationExtension B) C) :
    IsWeaklyCompact B := by
  apply isWeaklyCompact_of_twoSidedUnitizationExtension B
  exact isWeaklyCompact_of_rowColumn_total
    (twoSidedUnitizationExtension B) C hC hrow

/-- Arbitrary projective-tensor duals on independent nonunital algebras
receive their canonical separately weak-star continuous extension once the
single unitized analytic estimate is supplied. -/
theorem tensor_extension_data_of_unitizedRowColumn
    (f : StrongDual ℂ (Completion ℂ A D)) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate
      (twoSidedUnitizationExtension (tensorDualIsometry f)) C) :
    SeparatelyWeakStarContinuous
        (firstArens (tensorDualIsometry f)) ∧
      Extends (tensorDualIsometry f)
        (firstArens (tensorDualIsometry f)) ∧
      ‖firstArens (tensorDualIsometry f)‖ = ‖f‖ := by
  have hf : IsArensRegular f :=
    isWeaklyCompact_of_unitizedRowColumn
      (tensorDualIsometry f) C hC hrow
  refine ⟨separatelyWeakStarContinuous_firstExtension f hf,
    firstArens_canonical _, ?_⟩
  simpa only [norm_firstArens] using
    (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := D)).norm_map f

end TwoSidedUnitization

end

end MathlibAnnex.CStarBilinear
