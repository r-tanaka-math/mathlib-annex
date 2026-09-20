import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.ConstructedAverages
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal

/-!
# Pure-state homogeneity: the mathematical public boundary

Controller-authored integration candidate, UNBUILT. The public statements use
the existing project-independent state predicates. Legacy statement and
construction identities remain unchanged. No finite-average, Omega, row,
nuclearity or primitive-quotient simplicity premise is added.
-/
set_option autoImplicit false
noncomputable section
open Filter
namespace MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra
universe u

/-- The original unital-simple KOS proposition, discharged by constructed
averages in the source candidate rather than assumed as a parameter. -/
theorem kishimotoOzawaSakaiProperty_of_constructedAverages : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{u} :=
  MathlibAnnex.CStarAlgebra.kishimotoOzawaSakaiProperty_from_constructed_averages

/-- Mathematical form of the original point-norm consequence. -/
theorem exists_approximatelyInner_of_isPureState
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStarAlgebra A) (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) (hpsi : IsPureState A psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      (∀ a : A, phi (alpha a) = psi a) ∧
      ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
        ∃ v : unitary A, ∀ a ∈ F,
          ‖alpha a - (v : A) * a * star (v : A)‖ < epsilon :=
  MathlibAnnex.CStarAlgebra.kishimotoOzawaSakaiProperty_from_constructed_averages A hA phi psi hphi hpsi

/-- Same-kernel homogeneity for arbitrary separable unital C*-algebras. -/
theorem exists_asymptoticallyInner_of_isPureState_of_sameGNSKernel
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : stateGNSKernel phi = stateGNSKernel psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a :=
  MathlibAnnex.CStarAlgebra.sameKernel_exists_asymptoticallyInner_constructed phi psi hphi hpsi hker

/-- One alpha and one continuous path realize both forward and inverse
point-norm limits, and the state identity uses that same alpha. -/
theorem exists_twoSidedUnitaryPath_of_isPureState_of_sameGNSKernel
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : stateGNSKernel phi = stateGNSKernel psi) :
    ∃ (alpha : A ≃⋆ₐ[ℂ] A) (U : ℝ → unitary A),
      Continuous U ∧ U 0 = 1 ∧
      (∀ a : A, phi (alpha a) = psi a) ∧
      (∀ a : A, Tendsto (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t) a)
        atTop (nhds (alpha a))) ∧
      (∀ a : A, Tendsto (fun t ↦ (Unitary.conjStarAlgAut ℂ A (U t)).symm a)
        atTop (nhds (alpha.symm a))) := by
  obtain ⟨alpha, hpath, hstate⟩ :=
    exists_asymptoticallyInner_of_isPureState_of_sameGNSKernel phi psi hphi hpsi hker
  obtain ⟨U, hU, hU0, hlim⟩ := hpath
  exact ⟨alpha, U, hU, hU0, hstate, hlim,
    fun a ↦ tendsto_symm_apply_atTop_of_tendsto
      (fun t ↦ Unitary.conjStarAlgAut ℂ A (U t)) alpha hlim a⟩

/-- The actual GNS maps, rather than a predicate about zero sets of states,
can be used directly in the same-kernel assumption. -/
theorem exists_asymptoticallyInner_of_isPureState_of_gnsKernel_eq
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi)
    (hker : ∀ a : A,
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom a = 0 ↔
      (positiveLinearMapOfMemStateSpace psi hpsi.1).gnsStarAlgHom a = 0) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a : A, phi (alpha a) = psi a :=
  MathlibAnnex.CStarAlgebra.gnsKernel_exists_asymptoticallyInner_constructed phi psi hphi hpsi hker

/-- Genuinely nonunital same-kernel homogeneity; the continuous unitary path
belongs to the minimal unitization, not to an invented unit of A. -/
theorem exists_asymptoticallyInner_of_isPureNonUnitalState_of_gnsKernel_eq
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A]
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureNonUnitalState A phi) (hpsi : IsPureNonUnitalState A psi)
    (hker : ∀ a : A,
      (nonUnitalStatePositiveMap phi hphi.1).gnsNonUnitalStarAlgHom a = 0 ↔
      (nonUnitalStatePositiveMap psi hpsi.1).gnsNonUnitalStarAlgHom a = 0) :
    ∃ beta : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOneNonUnital beta ∧ ∀ a : A, phi (beta a) = psi a :=
  MathlibAnnex.CStarAlgebra.nonUnital_sameKernel_exists_asymptoticallyInner_constructed
    phi psi hphi hpsi hker

end MathlibAnnex.Analysis.CStarAlgebra
