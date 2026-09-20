import MathlibAnnex.Analysis.CStarAlgebra.CAR.CompletedSource
import MathlibAnnex.Algebra.Shell

/-!
# Difference shells in the completed CAR source

The decreasing root flag is converted to the orthogonal shell sequence used
by the analytic sum.  Matching is applied directly to these differences: no
difference of links for the nested flag projections is used.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The `n`-th orthogonal shell of the completed root flag. -/
noncomputable def rootShell (n : ℕ) : Limit :=
  rootFlag n - rootFlag (n + 1)

@[simp]
theorem rootShell_eq_shell (n : ℕ) :
    rootShell n = MathlibAnnex.Algebra.shell rootFlag n :=
  rfl

/-- Successive differences of the completed root flag are genuine star projections. -/
theorem isStarProjection_rootShell (n : ℕ) : IsStarProjection (rootShell n) := by
  have hmul : rootFlag n * rootFlag (n + 1) = rootFlag (n + 1) :=
    ((isStarProjection_rootFlag (n + 1)).le_iff_mul_eq_right
      (isStarProjection_rootFlag n)).1 (rootFlag_succ_le n)
  exact (isStarProjection_rootFlag (n + 1)).sub_of_mul_eq_right
    (isStarProjection_rootFlag n) hmul

@[simp]
theorem star_rootShell_mul_rootShell (n : ℕ) :
    star (rootShell n) * rootShell n = rootShell n := by
  rw [(isStarProjection_rootShell n).isSelfAdjoint.star_eq,
    (isStarProjection_rootShell n).isIdempotentElem.eq]

@[simp]
theorem rootShell_mul_star_rootShell (n : ℕ) :
    rootShell n * star (rootShell n) = rootShell n := by
  rw [(isStarProjection_rootShell n).isSelfAdjoint.star_eq,
    (isStarProjection_rootShell n).isIdempotentElem.eq]

/-- The first `N` genuine shells telescope to the complement of the `N`-th flag. -/
theorem sum_rootShell_range (N : ℕ) :
    ∑ n ∈ Finset.range N, rootShell n = 1 - rootFlag N := by
  calc
    ∑ n ∈ Finset.range N, rootShell n =
        ∑ n ∈ Finset.range N, MathlibAnnex.Algebra.shell rootFlag n := by
          simp only [rootShell_eq_shell]
    _ = rootFlag 0 - rootFlag N :=
      MathlibAnnex.Algebra.sum_shell_range rootFlag N
    _ = 1 - rootFlag N := by rw [rootFlag_zero]

/-- For each selected pure-state class, KOS chooses one automorphism and that
same automorphism matches every genuine difference shell. -/
theorem exists_representative_rootShell_family_of_kishimotoOzawaSakai
    (hKOS : MathlibAnnex.CStarAlgebra.KishimotoOzawaSakaiProperty.{0})
    (j : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ∃ alpha : Limit ≃⋆ₐ[ℂ] Limit,
      (∀ a : Limit,
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1 (alpha a) =
          completedRootPureState.1 a) ∧
      ∃ w : ℕ → Limit, ∀ n,
        star (w n) * w n = alpha (rootShell n) ∧
          w n * star (w n) = rootShell n := by
  exact MathlibAnnex.CStarAlgebra.exists_shell_family_of_kishimotoOzawaSakai hKOS Limit isSimpleCStarAlgebra_limit
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).1
    completedRootPureState.1
    (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState j).2
    completedRootPureState.2 rootShell isStarProjection_rootShell

/-- At the distinguished class the canonical choices are the identity
automorphism and the shells themselves. -/
theorem rootShell_identity_family :
    (∀ a : Limit,
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState
        completedRootPureState.classOf).1
          ((StarAlgEquiv.refl ℂ Limit) a) = completedRootPureState.1 a) ∧
    ∀ n,
      star (rootShell n) * rootShell n =
          (StarAlgEquiv.refl ℂ Limit) (rootShell n) ∧
        rootShell n * star (rootShell n) = rootShell n := by
  constructor
  · intro a
    simp
  · intro n
    exact ⟨star_rootShell_mul_rootShell n,
      rootShell_mul_star_rootShell n⟩

/-- Root compression transported by a star-algebra equivalence.  The inverse
is applied to the tested element; norm preservation is obtained from the
standard C-star equivalence API rather than added as source data. -/
theorem tendsto_norm_transported_compressionError
    (alpha : Limit ≃⋆ₐ[ℂ] Limit) (phi : Limit →L[ℂ] ℂ)
    (hstate : ∀ a : Limit, phi (alpha a) = rootState a)
    (b : Limit) :
    Tendsto
      (fun n ↦ ‖alpha (rootFlag n) * b * alpha (rootFlag n) -
        phi b • alpha (rootFlag n)‖)
      atTop (nhds 0) := by
  have hstate' : rootState (alpha.symm b) = phi b := by
    simpa using (hstate (alpha.symm b)).symm
  have hnorm (n : ℕ) :
      ‖alpha (rootFlag n) * b * alpha (rootFlag n) -
          phi b • alpha (rootFlag n)‖ =
        ‖compressionError n (alpha.symm b)‖ := by
    rw [← StarAlgEquiv.norm_map alpha (compressionError n (alpha.symm b))]
    simp [compressionError, hstate']
  exact (tendsto_norm_compressionError (alpha.symm b)).congr'
    (Filter.Eventually.of_forall fun n ↦ (hnorm n).symm)

/-- Vector-valued form of transported compression, used by represented
matrix-coefficient arguments. -/
theorem tendsto_transported_compressionError
    (alpha : Limit ≃⋆ₐ[ℂ] Limit) (phi : Limit →L[ℂ] ℂ)
    (hstate : ∀ a : Limit, phi (alpha a) = rootState a)
    (b : Limit) :
    Tendsto
      (fun n ↦ alpha (rootFlag n) * b * alpha (rootFlag n) -
        phi b • alpha (rootFlag n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_norm_transported_compressionError alpha phi hstate b

end MathlibAnnex.CStarAlgebra.CAR
