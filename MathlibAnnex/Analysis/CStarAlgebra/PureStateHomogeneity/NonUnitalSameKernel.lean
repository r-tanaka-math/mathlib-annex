import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.SameKernelTransport
import MathlibAnnex.Analysis.CStarAlgebra.State.NonUnitalGNSKernel
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.AsymptoticallyInner

/-!
# Same-GNS-kernel KOS on a genuinely nonunital source

C05 controller source, UNBUILT. The finite average existence theorem on
Unitization is explicitly pending source-author A. Apart from that shared
upstream premise, the unitization/purity/kernel/inverse/path restriction
steps are proof bodies here, not extra mathematical inputs to Codex.
-/
set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The concrete minimal unitization is separable when A is separable. -/
theorem separableSpace_unitization_of_separable
    [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (Unitization ℂ A) := by
  let e : Unitization ℂ A ≃ᵤ ℂ × A := Unitization.uniformEquivProd
  exact e.symm.surjective.denseRange.separableSpace e.symm.continuous

/-- General nonunital conclusion using the ACTUAL Mathlib GNS kernels.
No unit, simplicity, faithfulness, or equality of the two states is assumed. -/
theorem nonUnital_sameKernel_exists_asymptoticallyInner
    [TopologicalSpace.SeparableSpace A]
    (havg : HasRepresentationAverages (Unitization ℂ A))
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureNonUnitalState A phi) (hpsi : IsPureNonUnitalState A psi)
    (hker : ∀ a : A,
      (nonUnitalStatePositiveMap phi hphi.1).gnsNonUnitalStarAlgHom a = 0 ↔
      (nonUnitalStatePositiveMap psi hpsi.1).gnsNonUnitalStarAlgHom a = 0) :
    ∃ beta : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOneNonUnital beta ∧
        ∀ a : A, phi (beta a) = psi a := by
  letI : TopologicalSpace.SeparableSpace (Unitization ℂ A) :=
    separableSpace_unitization_of_separable (A := A)
  let Phi := unitizationExtension phi
  let Psi := unitizationExtension psi
  have hPhi : IsPureState (Unitization ℂ A) Phi :=
    isPureState_unitizationExtension phi hphi.1 hphi
  have hPsi : IsPureState (Unitization ℂ A) Psi :=
    isPureState_unitizationExtension psi hpsi.1 hpsi
  have hkerU : stateGNSKernel Phi = stateGNSKernel Psi :=
    unitizationExtension_stateGNSKernel_eq_of_nonUnital_gnsKernel_eq
      phi psi hphi.1 hpsi.1 hker
  obtain ⟨alpha, halpha, heq⟩ :=
    sameKernel_exists_asymptoticallyInner_of_representationAverages
      havg Phi Psi hPhi hPsi hkerU
  let beta : A ≃⋆ₐ[ℂ] A := unitizationRestrictEquiv alpha halpha.unitization_fst
  refine ⟨beta, halpha.restrict_nonUnital, ?_⟩
  intro a
  have h := heq (Unitization.inr a)
  rw [← unitizationRestrictEquiv_inr alpha halpha.unitization_fst a] at h
  simpa only [Phi, Psi, unitizationExtension_inr] using h

/-- Equivalent representation-independent square-test statement. -/
theorem nonUnital_squareKernel_exists_asymptoticallyInner
    [TopologicalSpace.SeparableSpace A]
    (havg : HasRepresentationAverages (Unitization ℂ A))
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureNonUnitalState A phi) (hpsi : IsPureNonUnitalState A psi)
    (hker : nonUnitalStateGNSKernel phi = nonUnitalStateGNSKernel psi) :
    ∃ beta : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOneNonUnital beta ∧
        ∀ a : A, phi (beta a) = psi a := by
  apply nonUnital_sameKernel_exists_asymptoticallyInner havg phi psi hphi hpsi
  intro a
  rw [← mem_nonUnitalStateGNSKernel_iff phi hphi.1 a,
    ← mem_nonUnitalStateGNSKernel_iff psi hpsi.1 a, hker]

end MathlibAnnex.CStarAlgebra
