import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic

/-!
# Vector functionals of Hilbert-space representations

This file bundles the coefficient `a ↦ ⟨ξ, π(a)ξ⟩` as a continuous
complex-linear functional.  No cyclicity, irreducibility, or dimension
hypothesis is imposed on the target Hilbert space.
-/

set_option autoImplicit false

open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Representation

/-- A star representation, regarded as a contractive continuous linear map
into the represented operator algebra. -/
noncomputable def continuousLinearMap (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi
      map_add' := map_add pi
      map_smul' := map_smul pi } 1 fun a ↦ by
    change ‖pi a‖ ≤ 1 * ‖a‖
    have hcoe : pi.toNonUnitalStarAlgHom a = pi a :=
      congrFun (StarAlgHom.coe_toNonUnitalStarAlgHom pi) a
    simpa only [one_mul, hcoe] using
      NonUnitalStarAlgHom.norm_apply_le pi.toNonUnitalStarAlgHom a

@[simp]
theorem continuousLinearMap_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    continuousLinearMap pi a = pi a :=
  rfl

/-- The continuous vector functional `a ↦ ⟨ξ, π(a)ξ⟩`.  Our inner-product
convention is conjugate-linear in the first argument and linear in the
second. -/
noncomputable def vectorFunctional (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp
    ((ContinuousLinearMap.apply ℂ H ξ).comp (continuousLinearMap pi))

@[simp]
theorem vectorFunctional_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    vectorFunctional pi ξ a = inner ℂ ξ (pi a ξ) :=
  rfl

/-- The vector functional records the full Gram kernel of the represented
orbit. -/
theorem vectorFunctional_star_mul
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a b : A) :
    vectorFunctional pi ξ (star a * b) = inner ℂ (pi a ξ) (pi b ξ) := by
  rw [vectorFunctional_apply]
  have hadj : ContinuousLinearMap.adjoint (pi a) = pi (star a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  have hmul : pi (star a * b) ξ = pi (star a) (pi b ξ) := by
    rw [map_mul]
    rfl
  rw [hmul, ← hadj, ContinuousLinearMap.adjoint_inner_right]

/-- Vector functionals are positive on positive elements. -/
theorem vectorFunctional_nonnegative (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {a : A} (ha : 0 ≤ a) : 0 ≤ vectorFunctional pi ξ a := by
  rw [vectorFunctional_apply]
  have hpa : 0 ≤ pi a := by
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        refine AddSubmonoid.subset_closure ⟨pi b, ?_⟩
        change star (pi b) * pi b = pi (star b * b)
        rw [map_mul, map_star]
    | zero => simp
    | add x y _ _ hx hy => simpa using AddSubmonoid.add_mem _ hx hy
  simpa using hpa.inner_nonneg_right ξ

/-- A unit vector gives a normalized vector functional. -/
theorem vectorFunctional_one (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {ξ : H} (hξ : ‖ξ‖ = 1) :
    vectorFunctional pi ξ 1 = 1 := by
  rw [vectorFunctional_apply, map_one]
  simpa [norm_sq_eq_re_inner, hξ] using inner_self_eq_norm_sq_to_K ℂ ξ

/-- A vector functional defined by a unit vector is contractive. -/
theorem norm_vectorFunctional_apply_le (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ξ : H} (hξ : ‖ξ‖ = 1) (a : A) :
    ‖vectorFunctional pi ξ a‖ ≤ ‖a‖ := by
  rw [vectorFunctional_apply]
  calc
    ‖inner ℂ ξ (pi a ξ)‖ ≤ ‖ξ‖ * ‖pi a ξ‖ := norm_inner_le_norm _ _
    _ = ‖pi a ξ‖ := by rw [hξ, one_mul]
    _ ≤ ‖pi a‖ * ‖ξ‖ := (pi a).le_opNorm ξ
    _ = ‖pi a‖ := by rw [hξ, mul_one]
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le pi a

/-- Moving a vector by a represented element pulls its vector functional back
by the corresponding `star u * a * u` expression. -/
theorem vectorFunctional_map_apply
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (u a : A) :
    vectorFunctional pi (pi u ξ) a =
      vectorFunctional pi ξ (star u * a * u) := by
  rw [vectorFunctional_apply, vectorFunctional_apply]
  have hadj : ContinuousLinearMap.adjoint (pi u) = pi (star u) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  calc
    inner ℂ (pi u ξ) (pi a (pi u ξ)) =
        inner ℂ ξ (ContinuousLinearMap.adjoint (pi u) (pi a (pi u ξ))) :=
      (ContinuousLinearMap.adjoint_inner_right (pi u) ξ (pi a (pi u ξ))).symm
    _ = inner ℂ ξ (pi (star u * a * u) ξ) := by
      rw [hadj, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
