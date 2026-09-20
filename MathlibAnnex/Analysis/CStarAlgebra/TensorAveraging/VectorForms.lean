import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import MathlibAnnex.Analysis.Normed.Bilinear.Bidual

/-!
# Reflexive-factor and C*-vector-form applications

This file supplies genuine infinite-dimensional and C*-algebraic uses of
the weak-compactness/Arens criterion.  In the complex example the coefficient
map lands in `H*`; it never treats the conjugate-linear Riesz map as linear.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped CStarAlgebra InnerProductSpace ComplexConjugate lp

namespace MathlibAnnex

noncomputable section

namespace WeakCompact

/-- The real Hilbert form on `ℓ²(ℕ)` as an ordinary bounded bilinear
form. -/
def realL2InnerForm :
    ℓ²(ℕ, ℝ) →L[ℝ] ℓ²(ℕ, ℝ) →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun x y : ℓ²(ℕ, ℝ) ↦ inner ℝ x y)
    (by intros; rw [inner_add_left])
    (by intros; simp [inner_smul_left])
    (by intros; rw [inner_add_right])
    (by intros; simp [inner_smul_right])).mkContinuous₂ 1 fun x y ↦ by
      change |inner ℝ x y| ≤ 1 * ‖x‖ * ‖y‖
      simpa only [one_mul, Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) x y)

@[simp]
theorem realL2InnerForm_apply (x y : ℓ²(ℕ, ℝ)) :
    realL2InnerForm x y = inner ℝ x y := rfl

/-- `ℓ²(ℕ,ℝ)` is genuinely infinite-dimensional. -/
theorem not_finiteDimensional_realL2 :
    ¬ FiniteDimensional ℝ ℓ²(ℕ, ℝ) := by
  intro h
  letI : FiniteDimensional ℝ ℓ²(ℕ, ℝ) := h
  let b : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ) := default
  have hc := b.orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
  rw [Cardinal.mk_nat] at hc
  exact (lt_irrefl Cardinal.aleph0) hc

/-- The associated operator of the real inner-product form on the
infinite-dimensional space `ℓ²(ℕ)` is weakly compact by an actual
factorization through that Hilbert space. -/
theorem isWeaklyCompact_realL2InnerForm :
    IsWeaklyCompact realL2InnerForm := by
  simpa using isWeaklyCompact_of_factorization
    (ContinuousLinearMap.id ℝ ℓ²(ℕ, ℝ)) realL2InnerForm
    (isReflexive_innerProductSpace (𝕜 := ℝ) (H := ℓ²(ℕ, ℝ)))

/-- The real `ℓ²` form therefore has its genuine separately weak-star
continuous bidual extension. -/
theorem exists_realL2InnerForm_extension :
    ∃ C : BidualBilinear.BidualForm ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ),
      BidualBilinear.SeparatelyWeakStarContinuous C ∧
      BidualBilinear.Extends realL2InnerForm C ∧
      ‖C‖ = ‖realL2InnerForm‖ :=
  (BidualBilinear.isWeaklyCompact_iff_exists_extension
    realL2InnerForm).mp isWeaklyCompact_realL2InnerForm

end WeakCompact

namespace CStarAlgebra.VectorForms

open WeakCompact BidualBilinear

universe uA uH

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def representationCLM
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := map_smul ρ }
    1 fun a ↦ by
      change ‖ρ a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ρ a

/-- The represented vector map `b ↦ ρ(b)η`. -/
def representedVector
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : H) : A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H η).comp (representationCLM ρ)

@[simp]
theorem representedVector_apply
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η : H) (b : A) :
    representedVector ρ η b = ρ b η := rfl

private def coefficientMapLinear
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →ₗ[ℂ] StrongDual ℂ H where
  toFun a := (innerSL ℂ ξ).comp (ρ a)
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro v
    simp

/-- The linear coefficient map `a ↦ (v ↦ ⟨ξ,ρ(a)v⟩)`.  Its codomain is
the continuous dual; no conjugate-linear identification with `H` is used. -/
def coefficientMap
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →L[ℂ] StrongDual ℂ H :=
  (coefficientMapLinear ρ ξ).mkContinuous ‖ξ‖ fun a ↦ by
    calc
      ‖(innerSL ℂ ξ).comp (ρ a)‖ ≤ ‖innerSL ℂ ξ‖ * ‖ρ a‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖ξ‖ * ‖ρ a‖ := by rw [innerSL_apply_norm]
      _ ≤ ‖ξ‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_left
          (NonUnitalStarAlgHom.norm_apply_le ρ a) (norm_nonneg ξ)

@[simp]
theorem coefficientMap_apply
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) (v : H) :
    coefficientMap ρ ξ a v = inner ℂ ξ (ρ a v) := rfl

/-- The bilinear vector-product form, presented as its associated operator
`A → A*`. -/
def vectorProductForm
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    A →L[ℂ] A →L[ℂ] ℂ :=
  (FiniteApproximation.dualMap (representedVector ρ η)).comp
    (coefficientMap ρ ξ)

@[simp]
theorem vectorProductForm_apply
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (a b : A) :
    vectorProductForm ρ ξ η a b = inner ℂ ξ (ρ a (ρ b η)) := rfl

/-- The associated vector-product operator factors through `H*`, which is
reflexive because `H` is Hilbert. -/
theorem isWeaklyCompact_vectorProductForm
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    IsWeaklyCompact (vectorProductForm ρ ξ η) := by
  exact isWeaklyCompact_of_factorization
    (coefficientMap ρ ξ)
    (FiniteApproximation.dualMap (representedVector ρ η))
    (isReflexive_dual
      (isReflexive_innerProductSpace (𝕜 := ℂ) (H := H)))

/-- The explicit first Arens extension of a vector-product form. -/
def vectorProductExtension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    BidualForm ℂ A A :=
  firstArens (vectorProductForm ρ ξ η)

theorem separatelyWeakStarContinuous_vectorProductExtension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    SeparatelyWeakStarContinuous (vectorProductExtension ρ ξ η) := by
  have hEq := (isWeaklyCompact_iff_firstArens_eq_secondArens
    (vectorProductForm ρ ξ η)).mp
      (isWeaklyCompact_vectorProductForm ρ ξ η)
  refine ⟨continuousFirst_firstArens _, ?_⟩
  change ContinuousSecond (firstArens (vectorProductForm ρ ξ η))
  rw [hEq]
  exact continuousSecond_secondArens _

@[simp]
theorem vectorProductExtension_canonical
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (a b : A) :
    BidualForm.eval (vectorProductExtension ρ ξ η)
      (NormedSpace.inclusionInDoubleDual ℂ A a)
      (NormedSpace.inclusionInDoubleDual ℂ A b) =
      inner ℂ ξ (ρ a (ρ b η)) := by
  simp [vectorProductExtension]

@[simp]
theorem norm_vectorProductExtension
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    ‖vectorProductExtension ρ ξ η‖ = ‖vectorProductForm ρ ξ η‖ := by
  exact norm_firstArens _

end CStarAlgebra.VectorForms

end


end MathlibAnnex
