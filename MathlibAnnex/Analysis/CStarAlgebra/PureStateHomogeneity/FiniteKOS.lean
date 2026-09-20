import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.FiniteTransport

/-! Finite-dimensional simple specialization of the same-alpha KOS conclusion. -/

set_option autoImplicit false
noncomputable section
namespace MathlibAnnex.CStarAlgebra
open MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [FiniteDimensional ℂ A] [TopologicalSpace.SeparableSpace A]

theorem finite_simple_pure_states_same_alpha_from_one
    (hsimple : IsSimpleCStarAlgebra A)
    (phi psi : A →L[ℂ] ℂ)
    (hphi : IsPureState A phi) (hpsi : IsPureState A psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      (∀ a : A, phi (alpha a) = psi a) ∧
        IsAsymptoticallyInnerFromOne alpha := by
  obtain ⟨alpha, hasym, hstate⟩ :=
    (finitePathTransport_pure_of_simple_finite hsimple).exists_asymptoticallyInner
      phi hphi psi hpsi
  exact ⟨alpha, hstate, hasym⟩

end MathlibAnnex.CStarAlgebra
