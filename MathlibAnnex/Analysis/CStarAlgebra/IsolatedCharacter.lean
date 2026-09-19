import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Topology.Algebra.Indicator

/-!
# Projections from isolated characters

Under the Gelfand transform, the characteristic function of an isolated
character is a nonzero projection.  Its principal ideal inside the
commutative algebra is one-dimensional.
-/

set_option autoImplicit false

open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {D : Type u} [CommCStarAlgebra D] [Nontrivial D]

/-- An isolated character produces a nonzero projection `p` satisfying
`p * d = chi d • p` for every `d`. -/
theorem exists_projection_mul_eq_smul_of_isOpen_singleton
    (chi : WeakDual.characterSpace ℂ D)
    (hopen : IsOpen ({chi} : Set (WeakDual.characterSpace ℂ D))) :
    ∃ p : D, IsStarProjection p ∧ p ≠ 0 ∧
      ∀ d : D, p * d = chi d • p := by
  have hclopen : IsClopen ({chi} : Set (WeakDual.characterSpace ℂ D)) :=
    ⟨isClosed_singleton, hopen⟩
  let e : WeakDual.characterSpace ℂ D → ℂ :=
    Set.indicator ({chi} : Set (WeakDual.characterSpace ℂ D)) (fun _ => 1)
  have he : Continuous e := hclopen.continuous_indicator continuous_const
  let F : C(WeakDual.characterSpace ℂ D, ℂ) := ⟨e, he⟩
  have hF : IsStarProjection F := by
    rw [isStarProjection_iff']
    constructor
    · ext psi
      by_cases hpsi : psi = chi
      · simp [F, e, hpsi]
      · simp [F, e, hpsi]
    · ext psi
      by_cases hpsi : psi = chi
      · simp [F, e, hpsi]
      · simp [F, e, hpsi]
  let p : D := (gelfandStarTransform D).symm F
  have hp : IsStarProjection p := hF.map (gelfandStarTransform D).symm
  have hptransform : gelfandStarTransform D p = F :=
    (gelfandStarTransform D).apply_symm_apply F
  have hpvalue : chi p = 1 := by
    change (gelfandStarTransform D p) chi = 1
    rw [hptransform]
    simp [F, e]
  have hpne : p ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hpvalue
    exact zero_ne_one hpvalue
  refine ⟨p, hp, hpne, ?_⟩
  intro d
  apply (gelfandStarTransform D).injective
  ext psi
  change psi (p * d) = psi (chi d • p)
  by_cases hpsi : psi = chi
  · subst psi
    simp [hpvalue]
  · have hpzero : psi p = 0 := by
      change (gelfandStarTransform D p) psi = 0
      rw [hptransform]
      simp [F, e, hpsi]
    simp [hpzero]

end MathlibAnnex.Analysis.CStarAlgebra
