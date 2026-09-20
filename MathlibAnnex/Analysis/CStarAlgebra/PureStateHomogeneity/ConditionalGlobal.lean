import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.PureFamily

/-!
# Exact local-to-global interface for general KOS

This proves the formal downstream implication once all four fields of a
pure-state `FinitePathTransport` are actually supplied. The currently
unsupplied path fields are explicit in the hypothesis. This theorem is a
dependency check and is not a proof of general `KishimotoOzawaSakaiProperty`.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CStarAlgebra

open MathlibAnnex.CStarAlgebra

universe u

theorem kishimotoOzawaSakaiProperty_of_pure_finitePathTransport
    (htransport : ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A]
      [StarOrderedRing A] [TopologicalSpace.SeparableSpace A],
      IsSimpleCStarAlgebra A → FinitePathTransport (IsPureState A)) :
    KishimotoOzawaSakaiProperty.{u} := by
  intro A _ _ _ _ hsimple phi psi hphi hpsi
  obtain ⟨alpha, hasym, hstate⟩ :=
    (htransport A hsimple).exists_asymptoticallyInner phi hphi psi hpsi
  exact ⟨alpha, hstate, hasym.isPointNormApproximatelyInner⟩

end MathlibAnnex.CStarAlgebra
