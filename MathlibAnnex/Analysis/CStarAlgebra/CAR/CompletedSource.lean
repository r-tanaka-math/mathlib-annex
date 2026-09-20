import MathlibAnnex.Analysis.CStarAlgebra.CAR.Simplicity
import MathlibAnnex.Analysis.CStarAlgebra.CAR.ShellMatching
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PureStateRepresentatives

/-!
# Source data on the completed CAR algebra

The root product state and its common decreasing projection flag are constructed on
the actual completion. KOS remains an explicit theorem argument.
-/

set_option autoImplicit false

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The completed root state bundled with its directly proved purity. -/
noncomputable def completedRootPureState : MathlibAnnex.CStarAlgebra.PureState Limit :=
  ⟨rootState, isPureState_rootState⟩

@[simp]
theorem representative_completedRootPureState :
    MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState completedRootPureState.classOf =
      completedRootPureState :=
  MathlibAnnex.CStarAlgebra.PureState.representative_root _

/-- For a selected pure-state GNS class, one KOS automorphism transports its state
to the root state and supports every member of the common root flag. -/
theorem exists_representative_rootFlag_shell_family_of_kishimotoOzawaSakai
    (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0})
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ∃ alpha : Limit ≃⋆ₐ[ℂ] Limit,
      (∀ a : Limit,
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1 (alpha a) =
          completedRootPureState.1 a) ∧
      ∃ w : ℕ → Limit, ∀ n,
        star (w n) * w n = alpha (rootFlag n) ∧
          w n * star (w n) = rootFlag n := by
  exact MathlibAnnex.CStarAlgebra.exists_shell_family_of_kishimotoOzawaSakai hKOS Limit isSimpleCStarAlgebra_limit
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1
    completedRootPureState.1
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).2
    completedRootPureState.2 rootFlag isStarProjection_rootFlag

/-- A compiled two-shell use of the family theorem; both links use the same KOS
automorphism, not separately selected automorphisms. -/
theorem exists_two_representative_rootFlag_links_of_kishimotoOzawaSakai
    (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0}) (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ∃ alpha : Limit ≃⋆ₐ[ℂ] Limit,
      (∀ a : Limit,
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1 (alpha a) =
          completedRootPureState.1 a) ∧
      ∃ w₀ w₁ : Limit,
        (star w₀ * w₀ = alpha (rootFlag 0) ∧ w₀ * star w₀ = rootFlag 0) ∧
        (star w₁ * w₁ = alpha (rootFlag 1) ∧ w₁ * star w₁ = rootFlag 1) := by
  obtain ⟨alpha, hstate, w, hw⟩ :=
    exists_representative_rootFlag_shell_family_of_kishimotoOzawaSakai hKOS j
  exact ⟨alpha, hstate, w 0, w 1, hw 0, hw 1⟩

end MathlibAnnex.CStarAlgebra.CAR
