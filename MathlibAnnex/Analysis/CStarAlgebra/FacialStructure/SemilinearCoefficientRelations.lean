/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FiniteCoefficientRelations
import MathlibAnnex.LinearAlgebra.Dual.FiniteKernel
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Fintype.Option

/-!
# Algebraic semilinear transport of finite coefficient relations

No continuity or boundedness of the vector equivalences is assumed. The
scalar homomorphism is involutive and commutes with star; identity and
complex conjugation are the two required specializations. These hypotheses
are scalar identities, not any of the coefficient or closure conclusions.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type t} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation B K)
variable (hpi : pi.IsIrreducible) (hrho : rho.IsIrreducible)
variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]
variable (hσ : ∀ c : ℂ, σ (star c) = star (σ c))
variable (U V : H ≃ₛₗ[σ] K)

include hpi hrho hσ

/-- A zero finite coefficient sum transports along two equivalences with the
same scalar involution. The conjugations in the matrix criterion are retained. -/
theorem sum_matrixCoefficient_eq_zero_semilinear
    {ι : Type*} [Fintype ι] (x y : ι → H)
    (h : (∑ i, matrixCoefficient pi (x i) (y i)) = 0) :
    (∑ i, matrixCoefficient rho (U (x i)) (V (y i))) = 0 := by
  classical
  obtain ⟨C, hx, hy⟩ := (sum_matrixCoefficient_eq_zero_iff_exists_matrix pi hpi x y).1 h
  apply (sum_matrixCoefficient_eq_zero_iff_exists_matrix rho hrho
    (fun i => U (x i)) (fun i => V (y i))).2
  refine ⟨Matrix.of (fun j k => σ (C j k)), ?_, ?_⟩
  · intro k
    have hh := congrArg U (hx k)
    simpa only [map_sum, map_smulₛₗ, hσ, map_zero, Matrix.of_apply] using hh
  · intro j
    have hh := congrArg V (hy j)
    simpa only [map_sum, map_smulₛₗ, Matrix.of_apply] using hh

/-- The zero-relation transport is reversible, without boundedness. -/
theorem sum_matrixCoefficient_eq_zero_semilinear_iff
    {ι : Type*} [Fintype ι] (x y : ι → H) :
    (∑ i, matrixCoefficient rho (U (x i)) (V (y i))) = 0 ↔
      (∑ i, matrixCoefficient pi (x i) (y i)) = 0 := by
  constructor
  · intro h
    have hh := sum_matrixCoefficient_eq_zero_semilinear rho pi hrho hpi hσ
      U.symm V.symm (fun i => U (x i)) (fun i => V (y i)) h
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · exact sum_matrixCoefficient_eq_zero_semilinear pi rho hpi hrho hσ U V x y

/-- An arbitrary finite linear combination transports with the scalar map σ.
An Option index adds the negative distinguished coefficient; it also handles
an empty family without a separate nonempty hypothesis. -/
theorem matrixCoefficient_eq_sum_smul_semilinear
    {ι : Type*} [Fintype ι] (x y : ι → H) (z w : H) (c : ι → ℂ)
    (h : matrixCoefficient pi z w = ∑ i, c i • matrixCoefficient pi (x i) (y i)) :
    matrixCoefficient rho (U z) (V w) =
      ∑ i, σ (c i) • matrixCoefficient rho (U (x i)) (V (y i)) := by
  classical
  let X : Option ι → H := Option.elim' (-z) (fun i => c i • x i)
  let Y : Option ι → H := Option.elim' w y
  have hzero : (∑ i, matrixCoefficient pi (X i) (Y i)) = 0 := by
    simpa [X, Y, Fintype.sum_option, matrixCoefficient_neg_left,
      matrixCoefficient_smul_left, h] using
      (neg_add_cancel (∑ i, c i • matrixCoefficient pi (x i) (y i)))
  have hh := sum_matrixCoefficient_eq_zero_semilinear pi rho hpi hrho hσ U V X Y hzero
  have hrel : -matrixCoefficient rho (U z) (V w) +
      (∑ i, σ (c i) • matrixCoefficient rho (U (x i)) (V (y i))) = 0 := by
    simpa [X, Y, Fintype.sum_option, map_smulₛₗ, matrixCoefficient_neg_left,
      matrixCoefficient_smul_left] using hh
  have heq := congrArg
    (fun f : StrongDual ℂ B => matrixCoefficient rho (U z) (V w) + f) hrel
  simpa only [← add_assoc, add_neg_cancel, zero_add, add_zero] using heq.symm

/-- Finite intersections of coefficient kernels transport in both directions.
This is an algebraic consequence of the actual finite relation theorem. -/
theorem forall_matrixCoefficient_eq_zero_imp_semilinear_iff
    {ι : Type*} [Fintype ι] (x y : ι → H) (z w : H) :
    (∀ b : B, (∀ i, matrixCoefficient rho (U (x i)) (V (y i)) b = 0) →
      matrixCoefficient rho (U z) (V w) b = 0) ↔
    (∀ a : A, (∀ i, matrixCoefficient pi (x i) (y i) a = 0) →
      matrixCoefficient pi z w a = 0) := by
  classical
  have forward (x y : ι → H) (z w : H)
      (h : ∀ a : A, (∀ i, matrixCoefficient pi (x i) (y i) a = 0) →
        matrixCoefficient pi z w a = 0) :
      ∀ b : B, (∀ i, matrixCoefficient rho (U (x i)) (V (y i)) b = 0) →
        matrixCoefficient rho (U z) (V w) b = 0 := by
    obtain ⟨c, hc⟩ := (LinearMap.forall_eq_zero_imp_iff_exists_sum_smul
      (fun i => (matrixCoefficient pi (x i) (y i)).toLinearMap)
      (matrixCoefficient pi z w).toLinearMap).1 h
    have hc' : matrixCoefficient pi z w =
        ∑ i, c i • matrixCoefficient pi (x i) (y i) := by
      ext a
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply, smul_apply,
        ContinuousLinearMap.coe_coe] using LinearMap.congr_fun hc a
    have ht := matrixCoefficient_eq_sum_smul_semilinear pi rho hpi hrho hσ U V x y z w c hc'
    intro b hb
    rw [ht]
    simp [hb]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (LinearMap.forall_eq_zero_imp_iff_exists_sum_smul
      (fun i => (matrixCoefficient rho (U (x i)) (V (y i))).toLinearMap)
      (matrixCoefficient rho (U z) (V w)).toLinearMap).1 h
    have hc' : matrixCoefficient rho (U z) (V w) =
        ∑ i, c i • matrixCoefficient rho (U (x i)) (V (y i)) := by
      ext b
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply, smul_apply,
        ContinuousLinearMap.coe_coe] using LinearMap.congr_fun hc b
    have ht := matrixCoefficient_eq_sum_smul_semilinear rho pi hrho hpi hσ U.symm V.symm
      (fun i => U (x i)) (fun i => V (y i)) (U z) (V w) c hc'
    simp only [LinearEquiv.symm_apply_apply] at ht
    intro a ha
    rw [ht]
    simp [ha]
  · exact forward x y z w

/-- Kernel equality is respected, including its equality branch in later
quotient constructions. This concerns FUNCTIONAL kernels, not representation kernels. -/
theorem ker_matrixCoefficient_eq_semilinear_iff (x y z w : H) :
    (matrixCoefficient rho (U x) (V y)).ker =
        (matrixCoefficient rho (U z) (V w)).ker ↔
      (matrixCoefficient pi x y).ker = (matrixCoefficient pi z w).ker := by
  have h₁ := forall_matrixCoefficient_eq_zero_imp_semilinear_iff pi rho hpi hrho hσ U V
    (fun _ : Unit => x) (fun _ : Unit => y) z w
  have h₂ := forall_matrixCoefficient_eq_zero_imp_semilinear_iff pi rho hpi hrho hσ U V
    (fun _ : Unit => z) (fun _ : Unit => w) x y
  simp only [forall_const] at h₁ h₂
  constructor
  · intro h
    apply le_antisymm
    · exact h₁.mp (fun b hb => h.le hb)
    · exact h₂.mp (fun b hb => h.ge hb)
  · intro h
    apply le_antisymm
    · exact h₁.mpr (fun a ha => h.le ha)
    · exact h₂.mpr (fun a ha => h.ge ha)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
