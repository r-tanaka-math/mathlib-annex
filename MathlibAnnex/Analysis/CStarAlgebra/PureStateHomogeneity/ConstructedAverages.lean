import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.UnconditionalOmega
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.FiniteAverageAssembly
import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.NonUnitalSameKernel

/-!
# KOS consumers with the finite-average hypothesis discharged

C06 controller source candidate, UNBUILT. These statements target the
ORIGINAL KOSStmt and the existing same-kernel / minimal-unitization results.
No finite-average existence, Ω, row supplier, nuclearity or simplicity of a
primitive quotient is hidden in an additional hypothesis.

The declarations are not a claim of Lean kernel acceptance. The full inherited
C01--C05 and author-A proof chain still requires whole-source qualification.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarAlgebra
universe u

/-- The formerly assigned input now has a proof term in this source tree. -/
theorem representationAverages_constructed
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    HasRepresentationAverages A := by
  intro H _ _ _ _ pi hpi
  exact hasFiniteCentralAverages pi hpi

/-- Original main KOS statement, not a renamed weaker target. -/
theorem kishimotoOzawaSakaiProperty_from_constructed_averages : KishimotoOzawaSakaiProperty.{u} :=
  kishimotoOzawaSakaiProperty_of_representationAverages representationAverages_constructed

/-- Same GNS kernel on an arbitrary separable UNITAL C*-algebra. -/
theorem sameKernel_exists_asymptoticallyInner_constructed
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : stateGNSKernel phi = stateGNSKernel psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a :=
  sameKernel_exists_asymptoticallyInner_of_representationAverages
    (representationAverages_constructed A) phi psi hphi hpsi hker

/-- The same statement using the two ACTUAL GNS representations. -/
theorem gnsKernel_exists_asymptoticallyInner_constructed
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : ∀ a : A,
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom a = 0 ↔
      (positiveLinearMapOfMemStateSpace psi hpsi.1).gnsStarAlgHom a = 0) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a :=
  gnsKernel_exists_asymptoticallyInner_of_representationAverages
    (representationAverages_constructed A) phi psi hphi hpsi hker

/-- Genuinely NONUNITAL endpoint: actual GNS kernels, one restricted
self-equivalence, and the SAME start-at-one unitization path. -/
theorem nonUnital_sameKernel_exists_asymptoticallyInner_constructed
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureNonUnitalState A phi) (hpsi : IsPureNonUnitalState A psi)
    (hker : ∀ a : A,
      (nonUnitalStatePositiveMap phi hphi.1).gnsNonUnitalStarAlgHom a = 0 ↔
      (nonUnitalStatePositiveMap psi hpsi.1).gnsNonUnitalStarAlgHom a = 0) :
    ∃ beta : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOneNonUnital beta ∧ ∀ a : A, phi (beta a) = psi a :=
  nonUnital_sameKernel_exists_asymptoticallyInner
    (representationAverages_constructed (Unitization ℂ A)) phi psi hphi hpsi hker

end MathlibAnnex.CStarAlgebra
