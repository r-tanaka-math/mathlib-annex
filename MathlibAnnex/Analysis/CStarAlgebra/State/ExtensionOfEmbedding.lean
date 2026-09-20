import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.CStarAlgebra.State.Extension

/-!
# Extending a normalized functional along a faithful C⋆-embedding

The source functional is transported to the actual linear range of the
embedding and extended by norm-preserving Hahn–Banach. No universal property
of the codomain, and no existence of a codomain representation, is assumed.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} {D : Type v} [CStarAlgebra A] [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

private noncomputable def rangePreimage (j : A →⋆ₐ[ℂ] D)
    (x : LinearMap.range j.toLinearMap) : A :=
  Classical.choose x.property

private theorem map_rangePreimage (j : A →⋆ₐ[ℂ] D)
    (x : LinearMap.range j.toLinearMap) : j (rangePreimage j x) = x :=
  Classical.choose_spec x.property

private noncomputable def rangeInverse (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) : LinearMap.range j.toLinearMap →ₗ[ℂ] A where
  toFun := rangePreimage j
  map_add' x y := by
    apply hj
    rw [map_add, map_rangePreimage, map_rangePreimage, map_rangePreimage]
    rfl
  map_smul' c x := by
    apply hj
    rw [map_smul, map_rangePreimage, map_rangePreimage]
    rfl

private theorem rangeInverse_map (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) (a : A) :
    rangeInverse j hj ⟨j a, ⟨a, rfl⟩⟩ = a := by
  apply hj
  exact map_rangePreimage j _

private theorem norm_rangeInverse (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) (x : LinearMap.range j.toLinearMap) :
    ‖rangeInverse j hj x‖ = ‖x‖ := by
  calc
    ‖rangeInverse j hj x‖ = ‖j (rangeInverse j hj x)‖ :=
      (NonUnitalStarAlgHom.norm_map j hj _).symm
    _ = ‖x‖ := by rw [show j (rangeInverse j hj x) = (x : D) from
      map_rangePreimage j x]; rfl

private noncomputable def rangeFunctional (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a, ‖τ a‖ ≤ ‖a‖) : LinearMap.range j.toLinearMap →L[ℂ] ℂ :=
  (τ.toLinearMap.comp (rangeInverse j hj)).mkContinuous 1 fun x ↦ by
    change ‖τ (rangeInverse j hj x)‖ ≤ 1 * ‖x‖
    rw [one_mul, ← norm_rangeInverse j hj x]
    exact hτ (rangeInverse j hj x)

private theorem norm_rangeFunctional_le (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a, ‖τ a‖ ≤ ‖a‖) : ‖rangeFunctional j hj τ hτ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖τ (rangeInverse j hj x)‖ ≤ 1 * ‖x‖
  simpa only [one_mul, norm_rangeInverse] using hτ (rangeInverse j hj x)

/-- A normalized contractive functional extends along an injective unital
C⋆-homomorphism to a state of its actual codomain. -/
theorem exists_state_extension_of_injective (j : A →⋆ₐ[ℂ] D)
    (hj : Function.Injective j) (τ : A →L[ℂ] ℂ)
    (hτ_one : τ 1 = 1) (hτ_norm : ∀ a, ‖τ a‖ ≤ ‖a‖) :
    ∃ φ : D →L[ℂ] ℂ, φ ∈ stateSpace D ∧ ∀ a, φ (j a) = τ a := by
  let M : Submodule ℂ D := LinearMap.range j.toLinearMap
  let f : M →L[ℂ] ℂ := rangeFunctional j hj τ hτ_norm
  obtain ⟨φ, hφ, hnorm⟩ := exists_extension_norm_eq M f
  have hrestrict (a : A) : φ (j a) = τ a := by
    calc
      φ (j a) = f ⟨j a, ⟨a, rfl⟩⟩ := hφ ⟨j a, ⟨a, rfl⟩⟩
      _ = τ (rangeInverse j hj ⟨j a, ⟨a, rfl⟩⟩) := rfl
      _ = τ a := by rw [rangeInverse_map]
  have hone : φ 1 = 1 := by simpa only [map_one, hτ_one] using hrestrict 1
  have hbound : ‖φ‖ ≤ 1 := by
    rw [hnorm]
    exact norm_rangeFunctional_le j hj τ hτ_norm
  letI : Nontrivial D := nontrivial_of_ne (1 : D) 0 (by
    intro hzero
    have h := hone
    rw [hzero, map_zero] at h
    exact zero_ne_one h)
  exact ⟨φ, ⟨nonnegative_of_norm_le_one_of_apply_one φ hbound hone, hone⟩,
    hrestrict⟩

end MathlibAnnex.Analysis.CStarAlgebra
