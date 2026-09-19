import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSum

/-!
# Atomic representations on dependent Hilbert sums

An arbitrary set-indexed family of Hilbert-space representations acts
coordinatewise on Mathlib's dependent Hilbert sum.  No separability,
countability, finite-index, or common-fiber hypothesis is used.
-/

set_option autoImplicit false

open scoped CStarAlgebra ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [CStarAlgebra A]
variable {I : Type v} {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

open MathlibAnnex.Analysis.InnerProductSpace

/-- The bounded coordinatewise action of one algebra element. -/
noncomputable def atomicAction
    (pi : ∀ i, Representation A (H i)) (a : A) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  diagonal (fun i ↦ pi i a) ‖a‖ (norm_nonneg a)
    (fun i ↦ NonUnitalStarAlgHom.norm_apply_le (pi i) a)

@[simp]
theorem atomicAction_apply
    (pi : ∀ i, Representation A (H i)) (a : A)
    (x : HilbertSum H) (i : I) :
    atomicAction pi a x i = pi i a (x i) :=
  rfl

/-- The genuine arbitrary-index atomic direct-sum representation. -/
noncomputable def atomicRepresentation
    (pi : ∀ i, Representation A (H i)) :
    Representation A (HilbertSum H) where
  toFun := atomicAction pi
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp [ContinuousLinearMap.mul_apply]
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    simp
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext i
    change pi i (algebraMap ℂ A c) (x i) = c • x i
    rw [← ContinuousLinearMap.algebraMap_apply (R := ℂ) (S := ℂ)
      (M := H i)]
    exact congrArg (fun T : H i →L[ℂ] H i ↦ T (x i)) ((pi i).commutes c)
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [lp.inner_eq_tsum, ContinuousLinearMap.adjoint_inner_left,
      lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    simp only [atomicAction_apply]
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (pi i a) (y i) (x i)

@[simp]
theorem atomicRepresentation_apply
    (pi : ∀ i, Representation A (H i)) (a : A)
    (x : HilbertSum H) (i : I) :
    atomicRepresentation pi a x i = pi i a (x i) :=
  rfl

@[simp]
theorem atomicRepresentation_single
    [DecidableEq I] (pi : ∀ i, Representation A (H i))
    (a : A) (i : I) (x : H i) :
    atomicRepresentation pi a (lp.single 2 i x) =
      lp.single 2 i (pi i a x) := by
  classical
  apply lp.ext
  funext j
  simp only [atomicRepresentation_apply, lp.coeFn_single]
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.single_apply, hji]

/-- One faithful summand makes the whole atomic representation faithful. -/
theorem atomicRepresentation_injective_of_component
    (pi : ∀ i, Representation A (H i)) (i : I)
    (hi : Function.Injective (pi i)) :
    Function.Injective (atomicRepresentation pi) := by
  classical
  intro a b hab
  apply hi
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg
    (fun T : HilbertSum H →L[ℂ] HilbertSum H ↦ T (lp.single 2 i x)) hab
  have hc := congrArg (fun y : HilbertSum H ↦ y i) h
  simpa using hc

/-- Fiberwise unitary intertwiners assemble into a unitary intertwiner of the
arbitrary dependent atomic sums. -/
theorem atomicRepresentation_unitaryEquivalent
    {K : I → Type*}
    [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
    [∀ i, CompleteSpace (K i)]
    (pi : ∀ i, Representation A (H i))
    (rho : ∀ i, Representation A (K i))
    (U : ∀ i, H i ≃ₗᵢ[ℂ] K i)
    (hU : ∀ i a x, U i (pi i a x) = rho i a (U i x)) :
    (atomicRepresentation pi).UnitaryEquivalent (atomicRepresentation rho) := by
  refine ⟨diagonalLinearIsometryEquiv U, ?_⟩
  intro a x
  apply lp.ext
  funext i
  simpa using hU i a (x i)

end MathlibAnnex.Analysis.CStarAlgebra
