import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-! Honest conditional use of the sole KOS boundary. -/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra

universe u

/-- Direct specialization of the KOS boundary; no source or target conclusion is assumed. -/
theorem pureState_transport_of_kishimotoOzawaSakai (hKOS : KishimotoOzawaSakaiProperty.{u})
    (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace A] (hsimple : IsSimpleCStarAlgebra A)
    (phi psi : A →L[ℂ] ℂ) (hphi : IsPureState A phi) (hpsi : IsPureState A psi) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      (∀ a : A, phi (alpha a) = psi a) ∧
      ∀ (F : Finset A) (epsilon : ℝ), 0 < epsilon →
        ∃ v : unitary A, ∀ a ∈ F,
          ‖alpha a - (v : A) * a * star (v : A)‖ < epsilon := by
  exact hKOS A hsimple phi psi hphi hpsi

end MathlibAnnex.CStarAlgebra
