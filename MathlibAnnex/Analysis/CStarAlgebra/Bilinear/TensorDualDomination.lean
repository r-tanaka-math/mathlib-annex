import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Factorization
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.TensorDual

/-!
# Positive domination for projective-tensor duals

This file connects the positive-functional Hilbert factorization to the
existing canonical projective-tensor dual and Arens-extension API.  It adds
no tensor norm and makes the still-required domination data explicit.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.ProjectiveTensorProduct

open MathlibAnnex.BidualBilinear
open MathlibAnnex.CStarBilinear
open MathlibAnnex.WeakCompact

universe uA uD

noncomputable section

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [NonUnitalCStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- Positive two-sided strong-star domination of the bilinear form represented
by a tensor-dual functional supplies actual Arens regularity. -/
theorem isArensRegular_of_strongStarDominated
    (f : StrongDual ℂ (Completion ℂ A D))
    (phi : A →L[ℂ] ℂ) (psi : D →L[ℂ] ℂ) (C : ℝ)
    (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (hpsi : ∀ d : D, 0 ≤ d → 0 ≤ psi d)
    (hC : 0 ≤ C)
    (hdom : IsStrongStarDominated (tensorDualIsometry f) phi psi C) :
    IsArensRegular f :=
  isWeaklyCompact_of_strongStarDominated
    (tensorDualIsometry f) phi psi C hphi hpsi hC hdom

/-- The canonical first Arens extension of a dominated tensor-dual functional
is separately weak-star continuous, extends the original form, and preserves
its norm. -/
theorem extension_data_of_strongStarDominated
    (f : StrongDual ℂ (Completion ℂ A D))
    (phi : A →L[ℂ] ℂ) (psi : D →L[ℂ] ℂ) (C : ℝ)
    (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (hpsi : ∀ d : D, 0 ≤ d → 0 ≤ psi d)
    (hC : 0 ≤ C)
    (hdom : IsStrongStarDominated (tensorDualIsometry f) phi psi C) :
    SeparatelyWeakStarContinuous
        (firstArens (tensorDualIsometry f)) ∧
      Extends (tensorDualIsometry f)
        (firstArens (tensorDualIsometry f)) ∧
      ‖firstArens (tensorDualIsometry f)‖ = ‖f‖ := by
  have hf : IsArensRegular f :=
    isArensRegular_of_strongStarDominated
      f phi psi C hphi hpsi hC hdom
  refine ⟨separatelyWeakStarContinuous_firstExtension f hf,
    firstArens_canonical _, ?_⟩
  simpa only [norm_firstArens] using
    (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := D)).norm_map f

/-- Under the same domination, the two canonical tensor-dual extensions
coincide. -/
theorem tensor_extensions_eq_of_strongStarDominated
    (f : StrongDual ℂ (Completion ℂ A D))
    (phi : A →L[ℂ] ℂ) (psi : D →L[ℂ] ℂ) (C : ℝ)
    (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (hpsi : ∀ d : D, 0 ≤ d → 0 ≤ psi d)
    (hC : 0 ≤ C)
    (hdom : IsStrongStarDominated (tensorDualIsometry f) phi psi C) :
    firstExtensionFunctional f = secondExtensionFunctional f :=
  (isArensRegular_iff_tensor_extensions_eq f).mp
    (isArensRegular_of_strongStarDominated
      f phi psi C hphi hpsi hC hdom)

end

end MathlibAnnex.ProjectiveTensorProduct
