/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Basic
import MathlibAnnex.Analysis.Normed.Module.DualKernel
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Projective uniqueness and two-term rank-one coefficient relations

All tests in this file take place in the full operator space. No assertion is
made that a rank-one test operator belongs to a given representation image.
Neither inner product space is required to be complete or finite-dimensional.
The two-term obstruction is algebraic: separating linear forms on the source
turn a putative rank-one sum into proportionality of the two target lines.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

@[simp]
theorem matrixCoefficient_neg_left (x : E) (y : F) :
    matrixCoefficient 𝕜 (-x) y = -matrixCoefficient 𝕜 x y := by
  ext T
  simp only [matrixCoefficient_apply, map_neg, inner_neg_right,
    ContinuousLinearMap.neg_apply]

/-- Rank-one tests convert a coefficient equality into a vector equality. -/
theorem inner_smul_eq_of_matrixCoefficient_eq_smul
    {x z : E} {y w : F} {c : 𝕜}
    (h : matrixCoefficient 𝕜 z w = c • matrixCoefficient 𝕜 x y) (v : F) :
    inner 𝕜 w v • z = c • (inner 𝕜 y v • x) := by
  apply ext_inner_left 𝕜
  intro u
  have hu := congrArg
    (fun f : (E →L[𝕜] F) →L[𝕜] 𝕜 => f (rankOne 𝕜 v u)) h
  simpa only [matrixCoefficient_apply_rankOne, ContinuousLinearMap.smul_apply,
    smul_eq_mul, inner_smul_right, mul_assoc, mul_comm, mul_left_comm] using hu

/-- The same test retains both coefficients of a two-term relation. -/
theorem inner_smul_eq_add_of_matrixCoefficient_eq_smul_add_smul
    {x₁ x₂ z : E} {y₁ y₂ w : F} {a b : 𝕜}
    (h : matrixCoefficient 𝕜 z w =
      a • matrixCoefficient 𝕜 x₁ y₁ + b • matrixCoefficient 𝕜 x₂ y₂) (v : F) :
    inner 𝕜 w v • z =
      a • (inner 𝕜 y₁ v • x₁) + b • (inner 𝕜 y₂ v • x₂) := by
  apply ext_inner_left 𝕜
  intro u
  have hu := congrArg
    (fun f : (E →L[𝕜] F) →L[𝕜] 𝕜 => f (rankOne 𝕜 v u)) h
  simpa only [matrixCoefficient_apply_rankOne, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, inner_smul_right, inner_add_right,
    mul_assoc, mul_comm, mul_left_comm] using hu

private theorem span_singleton_eq_of_nonzero_mem
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {x y : V} (hx : x ≠ 0) (hxy : x ∈ Submodule.span K {y}) :
    Submodule.span K {x} = Submodule.span K {y} := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxy
  have hc0 : c ≠ 0 := by
    intro hz
    apply hx
    simpa only [hz, zero_smul] using hc.symm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact hxy
  · apply Submodule.span_le.mpr
    intro z hz
    have hzy : z = y := Set.mem_singleton_iff.mp hz
    subst z
    have hy : c⁻¹ • x = y := by rw [← hc, inv_smul_smul₀ hc0]
    rw [← hy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- A nonzero coefficient determines both of its projective vector lines. -/
theorem span_eq_and_span_eq_of_matrixCoefficient_eq_smul
    {x z : E} {y w : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) {c : 𝕜}
    (h : matrixCoefficient 𝕜 z w = c • matrixCoefficient 𝕜 x y) :
    Submodule.span 𝕜 {x} = Submodule.span 𝕜 {z} ∧
      Submodule.span 𝕜 {y} = Submodule.span 𝕜 {w} := by
  have hww : inner 𝕜 w w ≠ 0 := inner_self_ne_zero.mpr hw
  let t : 𝕜 := (inner 𝕜 w w)⁻¹ * c * inner 𝕜 y w
  have hz' : z = t • x := by
    have hh := congrArg (fun v : E => (inner 𝕜 w w)⁻¹ • v)
      (inner_smul_eq_of_matrixCoefficient_eq_smul h w)
    simpa only [inv_smul_smul₀ hww, smul_smul, t, mul_assoc] using hh
  have ht : t ≠ 0 := by
    intro ht
    exact hz (by simpa only [ht, zero_smul] using hz')
  have hcoeff : matrixCoefficient 𝕜 x w = (t⁻¹ * c) • matrixCoefficient 𝕜 x y := by
    have hh := congrArg (fun f : (E →L[𝕜] F) →L[𝕜] 𝕜 => t⁻¹ • f) h
    simpa only [hz', matrixCoefficient_smul_left, inv_smul_smul₀ ht,
      smul_smul] using hh
  have hinj : Function.Injective (matrixCoefficient 𝕜 x : F → _) := by
    intro p q hpq
    have hh : matrixCoefficient 𝕜 x (p - q) = 0 := by
      rw [matrixCoefficient_sub_right, hpq, sub_self]
    exact sub_eq_zero.mp ((matrixCoefficient_eq_zero_iff.mp hh).resolve_left hx)
  have hw' : w = star (t⁻¹ * c) • y := by
    apply hinj
    rw [matrixCoefficient_smul_right, star_star]
    exact hcoeff
  refine ⟨(span_singleton_eq_of_nonzero_mem hz ?_).symm,
    (span_singleton_eq_of_nonzero_mem hw ?_).symm⟩
  · exact Submodule.mem_span_singleton.mpr ⟨t, hz'.symm⟩
  · exact Submodule.mem_span_singleton.mpr ⟨star (t⁻¹ * c), hw'.symm⟩

/-- Equality of two nonzero operator-coefficient kernels is equality of both lines. -/
theorem ker_matrixCoefficient_eq_iff_span_eq_and_span_eq
    {x z : E} {y w : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) :
    (matrixCoefficient 𝕜 x y).ker = (matrixCoefficient 𝕜 z w).ker ↔
      Submodule.span 𝕜 {x} = Submodule.span 𝕜 {z} ∧
      Submodule.span 𝕜 {y} = Submodule.span 𝕜 {w} := by
  constructor
  · intro h
    obtain ⟨c, _, hc⟩ :=
      (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
        (matrixCoefficient_ne_zero hx hy)).mp h
    exact span_eq_and_span_eq_of_matrixCoefficient_eq_smul hx hy hz hw hc
  · rintro ⟨hxz, hyw⟩
    have hzm : z ∈ Submodule.span 𝕜 {x} :=
      hxz.symm ▸ Submodule.subset_span (by simp)
    have hwm : w ∈ Submodule.span 𝕜 {y} :=
      hyw.symm ▸ Submodule.subset_span (by simp)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hzm
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hwm
    have ha0 : a ≠ 0 := by intro h; exact hz (by simpa [h] using ha.symm)
    have hb0 : b ≠ 0 := by intro h; exact hw (by simpa [h] using hb.symm)
    apply (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
      (matrixCoefficient_ne_zero hx hy)).mpr
    refine ⟨a * star b, mul_ne_zero ha0 (by simpa using hb0), ?_⟩
    rw [← ha, ← hb, matrixCoefficient_smul_left, matrixCoefficient_smul_right, smul_smul]

private theorem exists_coordinate_of_span_ne
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {x y : V} (hx : x ≠ 0)
    (hne : Submodule.span K {x} ≠ Submodule.span K {y}) :
    ∃ p : V →ₗ[K] K, p x = 1 ∧ p y = 0 := by
  have hnot : x ∉ Submodule.span K {y} := by
    intro hm
    exact hne (span_singleton_eq_of_nonzero_mem hx hm)
  obtain ⟨p, hpx, hp⟩ := Submodule.exists_le_ker_of_notMem hnot
  refine ⟨(p x)⁻¹ • p, ?_, ?_⟩
  · simp [hpx]
  · have hpy : p y = 0 := hp (Submodule.subset_span (by simp))
    simp [hpy]

/-- A rank-one coefficient cannot be a nontrivial sum with two independent
source lines AND two independent target lines. Scalars may be zero. -/
theorem eq_zero_or_eq_zero_of_matrixCoefficient_eq_smul_add_smul
    {x₁ x₂ z : E} {y₁ y₂ w : F}
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hx : Submodule.span 𝕜 {x₁} ≠ Submodule.span 𝕜 {x₂})
    (hy : Submodule.span 𝕜 {y₁} ≠ Submodule.span 𝕜 {y₂}) {a b : 𝕜}
    (h : matrixCoefficient 𝕜 z w =
      a • matrixCoefficient 𝕜 x₁ y₁ + b • matrixCoefficient 𝕜 x₂ y₂) :
    a = 0 ∨ b = 0 := by
  classical
  by_contra hab
  obtain ⟨ha, hb⟩ := not_or.mp hab
  obtain ⟨p, hp₁, hp₂⟩ := exists_coordinate_of_span_ne hx₁ hx
  obtain ⟨q, hq₂, hq₁⟩ := exists_coordinate_of_span_ne hx₂ hx.symm
  have ht (v : F) := inner_smul_eq_add_of_matrixCoefficient_eq_smul_add_smul h v
  have hp (v : F) : inner 𝕜 w v * p z = a * inner 𝕜 y₁ v := by
    have hh := congrArg p (ht v)
    simpa only [map_add, map_smul, smul_eq_mul, hp₁, hp₂,
      mul_one, mul_zero, add_zero] using hh
  have hq (v : F) : inner 𝕜 w v * q z = b * inner 𝕜 y₂ v := by
    have hh := congrArg q (ht v)
    simpa only [map_add, map_smul, smul_eq_mul, hq₁, hq₂,
      mul_one, mul_zero, zero_add] using hh
  have hy₁w : y₁ = star (p z / a) • w := by
    apply ext_inner_right 𝕜
    intro v
    have hh : inner 𝕜 y₁ v = (p z / a) * inner 𝕜 w v := by
      apply (mul_left_cancel₀ ha)
      calc
        a * inner 𝕜 y₁ v = inner 𝕜 w v * p z := (hp v).symm
        _ = a * ((p z / a) * inner 𝕜 w v) := by field_simp [ha] <;> ring
    simpa [inner_smul_left, RCLike.star_def] using hh
  have hy₂w : y₂ = star (q z / b) • w := by
    apply ext_inner_right 𝕜
    intro v
    have hh : inner 𝕜 y₂ v = (q z / b) * inner 𝕜 w v := by
      apply (mul_left_cancel₀ hb)
      calc
        b * inner 𝕜 y₂ v = inner 𝕜 w v * q z := (hq v).symm
        _ = b * ((q z / b) * inner 𝕜 w v) := by field_simp [hb] <;> ring
    simpa [inner_smul_left, RCLike.star_def] using hh
  apply hy
  have h₁ := span_singleton_eq_of_nonzero_mem hy₁
    (Submodule.mem_span_singleton.mpr ⟨star (p z / a), hy₁w.symm⟩)
  have h₂ := span_singleton_eq_of_nonzero_mem hy₂
    (Submodule.mem_span_singleton.mpr ⟨star (q z / b), hy₂w.symm⟩)
  exact h₁.trans h₂.symm

end InnerProductSpace
