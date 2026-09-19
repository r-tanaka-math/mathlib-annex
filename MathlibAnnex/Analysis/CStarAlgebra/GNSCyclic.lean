import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# The canonical cyclic vector in the unital GNS construction

Mathlib constructs the GNS Hilbert space and representation for a positive linear
functional.  This file records the canonical vector represented by the unit, proves
the vector-state formula with Mathlib's conjugate-linear-in-the-first-variable inner
product convention, and proves density of its algebra orbit.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A null vector for the positive-functional seminorm is orthogonal in the first slot.
This is the Cauchy--Schwarz step used to make dominated forms independent of representatives. -/
theorem apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero
    (f : A →ₚ[ℂ] ℂ) {a : A} (ha : f (star a * a) = 0) (b : A) :
    f (star a * b) = 0 := by
  have hnorm : ‖f.toPreGNS a‖ = 0 := by
    rw [preGNS_norm_def]
    simp [ha]
  have hbound := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS a) (f.toPreGNS b)
  rw [hnorm, zero_mul] at hbound
  have hinner : ⟪f.toPreGNS a, f.toPreGNS b⟫_ℂ = 0 :=
    norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  simpa [preGNS_inner_def] using hinner

/-- A null vector for the positive-functional seminorm is orthogonal in the second slot. -/
theorem apply_star_mul_eq_zero_of_apply_star_mul_self_eq_zero_right
    (f : A →ₚ[ℂ] ℂ) {a : A} (ha : f (star a * a) = 0) (b : A) :
    f (star b * a) = 0 := by
  have hnorm : ‖f.toPreGNS a‖ = 0 := by
    rw [preGNS_norm_def]
    simp [ha]
  have hbound := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS b) (f.toPreGNS a)
  rw [hnorm, mul_zero] at hbound
  have hinner : ⟪f.toPreGNS b, f.toPreGNS a⟫_ℂ = 0 :=
    norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  simpa [preGNS_inner_def] using hinner

/-- The canonical GNS vector represented by the unit of the algebra. -/
noncomputable def gnsCyclicVector (f : A →ₚ[ℂ] ℂ) : f.GNS :=
  (f.toPreGNS 1 : f.PreGNS)

@[simp]
theorem gnsStarAlgHom_apply_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a f.gnsCyclicVector = (f.toPreGNS a : f.GNS) := by
  rw [gnsCyclicVector]
  change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1 : f.GNS) = _
  rw [gnsNonUnitalStarAlgHom_apply_coe]
  congr 1
  change f.toPreGNS (a * 1) = f.toPreGNS a
  rw [mul_one]

/-- The GNS vector state is the original positive functional.  The vector occurs in
the first argument because Mathlib's complex inner product is conjugate-linear there. -/
@[simp]
theorem inner_gnsCyclicVector_gnsStarAlgHom (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪f.gnsCyclicVector, f.gnsStarAlgHom a f.gnsCyclicVector⟫_ℂ = f a := by
  rw [gnsStarAlgHom_apply_gnsCyclicVector, gnsCyclicVector,
    UniformSpace.Completion.inner_coe, preGNS_inner_def]
  simp

/-- A normalized positive functional gives a unit canonical GNS vector. -/
theorem norm_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) (h : f 1 = 1) :
    ‖f.gnsCyclicVector‖ = 1 := by
  rw [gnsCyclicVector, UniformSpace.Completion.norm_coe, preGNS_norm_def]
  simp [h]

/-- The algebra orbit of the canonical GNS vector is dense in the completed GNS space. -/
theorem denseRange_gnsStarAlgHom_apply_gnsCyclicVector (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A ↦ f.gnsStarAlgHom a f.gnsCyclicVector) := by
  have hpre : DenseRange (f.toPreGNS : A → f.PreGNS) :=
    f.toPreGNS.surjective.denseRange
  have hcomp := UniformSpace.Completion.denseRange_coe.comp hpre
    (UniformSpace.Completion.continuous_coe f.PreGNS)
  convert hcomp using 1
  funext a
  exact f.gnsStarAlgHom_apply_gnsCyclicVector a

end PositiveLinearMap
