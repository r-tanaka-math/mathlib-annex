/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Kernel

/-!
# Operators determined up to a scalar by coefficient zero sets

The main result generalizes Lemma 6.6 of arXiv:2504.05551v1, pp. 34--35.
Only the codomain needs an inner product; the domain is an arbitrary vector space.
Neither boundedness, completeness, finite dimension, nor a closed range is needed.

The proof is algebraic rather than a polar-decomposition argument. Orthogonal
annihilation first implies pointwise proportionality. One nonzero value of the
first map supplies a fixed coordinate functional. Its kernel determines a single
scalar, and addition of the selected vector handles the zero-coordinate case.
The zero-map case is included explicitly.
-/

set_option autoImplicit false

noncomputable section

namespace InnerProductSpace

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

private theorem exists_eq_smul_of_inner_eq_zero_imp (a b : F)
    (h : ∀ y : F, inner 𝕜 y a = 0 → inner 𝕜 y b = 0) :
    ∃ c : 𝕜, b = c • a := by
  by_cases ha : a = 0
  · have hb : inner 𝕜 b b = 0 := h b (by simp [ha])
    exact ⟨0, by simpa using (inner_self_eq_zero.mp hb)⟩
  have haa : inner 𝕜 a a ≠ 0 := inner_self_ne_zero.mpr ha
  let c : 𝕜 := inner 𝕜 a b / inner 𝕜 a a
  let z : F := b - c • a
  have haz : inner 𝕜 a z = 0 := by
    dsimp only [z]
    rw [inner_sub_right, inner_smul_right]
    dsimp only [c]
    rw [div_mul_cancel₀ _ haa, sub_self]
  have hza : inner 𝕜 z a = 0 := inner_eq_zero_symm.mp haz
  have hzb : inner 𝕜 z b = 0 := h z hza
  have hzz : inner 𝕜 z z = 0 := by
    change inner 𝕜 z (b - c • a) = 0
    rw [inner_sub_right, inner_smul_right, hzb, hza, mul_zero, sub_self]
  exact ⟨c, sub_eq_zero.mp (inner_self_eq_zero.mp hzz)⟩

end InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Orthogonal annihilation of every value of `A` implies that `B` is one
fixed scalar multiple of `A`. This includes `A = 0`. -/
theorem exists_eq_smul_of_forall_inner_eq_zero_imp (A B : E →ₗ[𝕜] F)
    (h : ∀ (x : E) (y : F), inner 𝕜 y (A x) = 0 → inner 𝕜 y (B x) = 0) :
    ∃ c : 𝕜, B = c • A := by
  classical
  by_cases hA : A = 0
  · refine ⟨0, ?_⟩
    ext x
    have hx : inner 𝕜 (B x) (B x) = 0 := h x (B x) (by simp [hA])
    simpa using (inner_self_eq_zero.mp hx)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, A x₀ ≠ 0 := by
    by_contra! hall
    exact hA (LinearMap.ext fun x => hall x)
  obtain ⟨c, hc⟩ :=
    InnerProductSpace.exists_eq_smul_of_inner_eq_zero_imp (A x₀) (B x₀) (h x₀)
  let f : F →ₗ[𝕜] 𝕜 := (innerSL 𝕜 (A x₀)).toLinearMap
  have hf : f (A x₀) ≠ 0 := inner_self_ne_zero.mpr hx₀
  have hcoord (x : E) : f (B x) = c * f (A x) := by
    let t : 𝕜 := f (A x) / f (A x₀)
    have hz : f (A (x - t • x₀)) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      dsimp only [t]
      rw [div_mul_cancel₀ _ hf, sub_self]
    have hzB : f (B (x - t • x₀)) = 0 := h (x - t • x₀) (A x₀) hz
    simp only [map_sub, map_smul, smul_eq_mul] at hzB
    rw [hc, map_smul, smul_eq_mul] at hzB
    have hmul : t * (c * f (A x₀)) = c * f (A x) := by
      dsimp only [t]
      field_simp [hf] <;> ring
    rw [hmul] at hzB
    exact sub_eq_zero.mp hzB
  have hgood (x : E) (hx : f (A x) ≠ 0) : B x = c • A x := by
    obtain ⟨d, hd⟩ :=
      InnerProductSpace.exists_eq_smul_of_inner_eq_zero_imp (A x) (B x) (h x)
    have heq := hcoord x
    rw [hd, map_smul, smul_eq_mul] at heq
    have hzero : (d - c) * f (A x) = 0 := by
      rw [sub_mul, heq, sub_self]
    have hdc : d = c := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hx)
    simpa only [hdc] using hd
  refine ⟨c, ?_⟩
  ext x
  change B x = c • A x
  by_cases hx : f (A x) = 0
  · have hsum : f (A (x + x₀)) ≠ 0 := by
      simpa only [map_add, hx, zero_add] using hf
    have heq := hgood (x + x₀) hsum
    rw [map_add, map_add, smul_add, hc] at heq
    exact add_right_cancel heq
  · exact hgood x hx

/-- The scalar is unique precisely once a nonzero first map is supplied. -/
theorem existsUnique_eq_smul_of_forall_inner_eq_zero_imp
    (A B : E →ₗ[𝕜] F) (hA : A ≠ 0)
    (h : ∀ (x : E) (y : F), inner 𝕜 y (A x) = 0 → inner 𝕜 y (B x) = 0) :
    ∃! c : 𝕜, B = c • A := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_inner_eq_zero_imp A B h
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (smul_left_injective 𝕜 hA) (hd.symm.trans hc)

end LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Bounded-operator specialization; only the target has an inner product. -/
theorem exists_eq_smul_of_forall_inner_eq_zero_imp (A B : E →L[𝕜] F)
    (h : ∀ (x : E) (y : F), inner 𝕜 y (A x) = 0 → inner 𝕜 y (B x) = 0) :
    ∃ c : 𝕜, B = c • A := by
  obtain ⟨c, hc⟩ :=
    LinearMap.exists_eq_smul_of_forall_inner_eq_zero_imp A.toLinearMap B.toLinearMap h
  refine ⟨c, ?_⟩
  ext x
  exact congrArg (fun T : E →ₗ[𝕜] F => T x) hc

end ContinuousLinearMap

namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The coefficient-zero-set criterion is equivalent to scalar proportionality
of the operators, not merely of scalar-valued functionals. -/
theorem forall_matrixCoefficient_eq_zero_imp_iff (A B : E →L[𝕜] F) :
    (∀ (x : E) (y : F), matrixCoefficient 𝕜 x y A = 0 →
      matrixCoefficient 𝕜 x y B = 0) ↔ ∃ c : 𝕜, B = c • A := by
  constructor
  · exact ContinuousLinearMap.exists_eq_smul_of_forall_inner_eq_zero_imp A B
  · rintro ⟨c, rfl⟩ x y hxy
    change inner 𝕜 y (c • A x) = 0
    rw [inner_smul_right, show inner 𝕜 y (A x) = 0 from hxy, mul_zero]

end InnerProductSpace
