/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment
import MathlibAnnex.Analysis.Normed.Module.DualKernel

/-!
# Linear and conjugate-linear coefficient kernels

The source slot is complex linear and the target slot is conjugate linear.
Irreducibility gives the exact coefficient norm, hence injectivity in either
slot when the other vector is nonzero. Equality of functional kernels is
then precisely equality of the corresponding one-dimensional subspaces.
Zero vectors are retained in the algebraic identities and excluded explicitly
only where a genuine projective line or a nonzero functional is required.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp]
theorem matrixCoefficient_zero_left (pi : NonUnitalCStarRepresentation A H) (y : H) :
    matrixCoefficient pi 0 y = 0 := by
  ext a
  simp only [matrixCoefficient_apply, map_zero, inner_zero_right,
    ContinuousLinearMap.zero_apply]

@[simp]
theorem matrixCoefficient_zero_right (pi : NonUnitalCStarRepresentation A H) (x : H) :
    matrixCoefficient pi x 0 = 0 := by
  ext a
  simp only [matrixCoefficient_apply, inner_zero_left, ContinuousLinearMap.zero_apply]

theorem matrixCoefficient_add_left (pi : NonUnitalCStarRepresentation A H) (x z y : H) :
    matrixCoefficient pi (x + z) y = matrixCoefficient pi x y + matrixCoefficient pi z y := by
  ext a
  simp only [matrixCoefficient_apply, map_add, inner_add_right,
    ContinuousLinearMap.add_apply]

theorem matrixCoefficient_add_right (pi : NonUnitalCStarRepresentation A H) (x y z : H) :
    matrixCoefficient pi x (y + z) = matrixCoefficient pi x y + matrixCoefficient pi x z := by
  ext a
  simp only [matrixCoefficient_apply, inner_add_left, ContinuousLinearMap.add_apply]

theorem matrixCoefficient_sub_left (pi : NonUnitalCStarRepresentation A H) (x z y : H) :
    matrixCoefficient pi (x - z) y = matrixCoefficient pi x y - matrixCoefficient pi z y := by
  ext a
  simp only [matrixCoefficient_apply, map_sub, inner_sub_right,
    ContinuousLinearMap.sub_apply]

theorem matrixCoefficient_sub_right (pi : NonUnitalCStarRepresentation A H) (x y z : H) :
    matrixCoefficient pi x (y - z) = matrixCoefficient pi x y - matrixCoefficient pi x z := by
  ext a
  simp only [matrixCoefficient_apply, inner_sub_left, ContinuousLinearMap.sub_apply]

theorem matrixCoefficient_smul_left (pi : NonUnitalCStarRepresentation A H)
    (c : ℂ) (x y : H) :
    matrixCoefficient pi (c • x) y = c • matrixCoefficient pi x y := by
  ext a
  simp only [matrixCoefficient_apply, map_smul, inner_smul_right,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem matrixCoefficient_smul_right (pi : NonUnitalCStarRepresentation A H)
    (c : ℂ) (x y : H) :
    matrixCoefficient pi x (c • y) = star c • matrixCoefficient pi x y := by
  ext a
  simp only [matrixCoefficient_apply, inner_smul_left, RCLike.star_def,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Exact nonzeroness in an irreducible representation, including both zero cases. -/
theorem matrixCoefficient_ne_zero_iff (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (x y : H) :
    matrixCoefficient pi x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_matrixCoefficient_of_isIrreducible pi hpi,
    mul_ne_zero_iff, norm_ne_zero_iff, norm_ne_zero_iff]

/-- The conjugate-linear target parametrization is injective for nonzero source. -/
theorem matrixCoefficient_right_injective (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) {x : H} (hx : x ≠ 0) :
    Function.Injective (matrixCoefficient pi x) := by
  intro y z heq
  have hz : matrixCoefficient pi x (y - z) = 0 := by
    rw [matrixCoefficient_sub_right, heq, sub_self]
  by_contra hne
  exact (matrixCoefficient_ne_zero_iff pi hpi x (y - z)).2
    ⟨hx, sub_ne_zero.mpr hne⟩ hz

/-- The linear source parametrization is injective for nonzero target. -/
theorem matrixCoefficient_left_injective (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) {y : H} (hy : y ≠ 0) :
    Function.Injective (fun x => matrixCoefficient pi x y) := by
  intro x z heq
  change matrixCoefficient pi x y = matrixCoefficient pi z y at heq
  have hz : matrixCoefficient pi (x - z) y = 0 := by
    rw [matrixCoefficient_sub_left, heq, sub_self]
  by_contra hne
  exact (matrixCoefficient_ne_zero_iff pi hpi (x - z) y).2
    ⟨sub_ne_zero.mpr hne, hy⟩ hz

/-- The proportionality scalar in the target slot must be conjugated. -/
theorem matrixCoefficient_eq_smul_iff_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x : H} (hx : x ≠ 0) (y z : H) (c : ℂ) :
    matrixCoefficient pi x z = c • matrixCoefficient pi x y ↔ z = star c • y := by
  have hc : c • matrixCoefficient pi x y = matrixCoefficient pi x (star c • y) := by
    rw [matrixCoefficient_smul_right, star_star]
  rw [hc]
  exact (matrixCoefficient_right_injective pi hpi hx).eq_iff

/-- The proportionality scalar in the source slot is not conjugated. -/
theorem matrixCoefficient_eq_smul_iff_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {y : H} (hy : y ≠ 0) (x z : H) (c : ℂ) :
    matrixCoefficient pi z y = c • matrixCoefficient pi x y ↔ z = c • x := by
  rw [← matrixCoefficient_smul_left]
  exact (matrixCoefficient_left_injective pi hpi hy).eq_iff

/-- Common-source kernel equality is nonzero proportionality of the targets. -/
theorem ker_matrixCoefficient_eq_iff_exists_ne_zero_smul_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x y z : H} (hx : x ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficient pi x y).ker = (matrixCoefficient pi x z).ker ↔
      ∃ c : ℂ, c ≠ 0 ∧ z = c • y := by
  rw [ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
    ((matrixCoefficient_ne_zero_iff pi hpi x y).2 ⟨hx, hy⟩)]
  constructor
  · rintro ⟨c, hc, heq⟩
    refine ⟨star c, by simpa using hc, ?_⟩
    exact (matrixCoefficient_eq_smul_iff_right pi hpi hx y z c).1 heq
  · rintro ⟨c, hc, rfl⟩
    exact ⟨star c, by simpa using hc, matrixCoefficient_smul_right pi c x y⟩

/-- Common-target kernel equality is nonzero proportionality of the sources. -/
theorem ker_matrixCoefficient_eq_iff_exists_ne_zero_smul_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x z y : H} (hx : x ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficient pi x y).ker = (matrixCoefficient pi z y).ker ↔
      ∃ c : ℂ, c ≠ 0 ∧ z = c • x := by
  rw [ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul
    ((matrixCoefficient_ne_zero_iff pi hpi x y).2 ⟨hx, hy⟩)]
  exact exists_congr fun c => and_congr_right fun _ =>
    matrixCoefficient_eq_smul_iff_left pi hpi hy x z c

/-- Normalizing nonzero source and target vectors preserves the functional kernel,
without any irreducibility or faithfulness hypothesis. -/
theorem exists_unit_vectors_ker_matrixCoefficient_eq
    (pi : NonUnitalCStarRepresentation A H) (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ v w : H, ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (matrixCoefficient pi v w).ker = (matrixCoefficient pi x y).ker := by
  let x' : H := (‖x‖ : ℂ)⁻¹ • x
  let y' : H := (‖y‖ : ℂ)⁻¹ • y
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hx' : ‖x'‖ = 1 := by
    simp only [x', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ hxn
  have hy' : ‖y'‖ = 1 := by
    simp only [y', norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact inv_mul_cancel₀ hyn
  have hker : (matrixCoefficient pi x' y').ker = (matrixCoefficient pi x y).ker := by
    ext a
    change matrixCoefficient pi x' y' a = 0 ↔ matrixCoefficient pi x y a = 0
    simp [x', y', matrixCoefficient_smul_left, matrixCoefficient_smul_right,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hxn, hyn]
  exact ⟨x', y', hx', hy', hker⟩

/-- Equality of two nonzero source or target lines, in scalar form. -/
private theorem span_singleton_eq_iff_exists_ne_zero_smul
    {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {x y : V} (hy : y ≠ 0) :
    Submodule.span 𝕜 {x} = Submodule.span 𝕜 {y} ↔
      ∃ c : 𝕜, c ≠ 0 ∧ y = c • x := by
  constructor
  · intro h
    have hym : y ∈ Submodule.span 𝕜 {x} := h.symm ▸ Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hym
    refine ⟨c, ?_, hc.symm⟩
    intro hzero
    apply hy
    simpa [hzero] using hc.symm
  · rintro ⟨c, hc, rfl⟩
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      apply Submodule.mem_span_singleton.mpr
      exact ⟨c⁻¹, inv_smul_smul₀ hc x⟩
    · apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))

/-- Paper 5.5: kernels with a common nonzero source determine the target line. -/
theorem ker_matrixCoefficient_eq_iff_span_eq_right
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x y z : H} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (matrixCoefficient pi x y).ker = (matrixCoefficient pi x z).ker ↔
      Submodule.span ℂ {y} = Submodule.span ℂ {z} := by
  rw [ker_matrixCoefficient_eq_iff_exists_ne_zero_smul_right pi hpi hx hy,
    span_singleton_eq_iff_exists_ne_zero_smul hz]

/-- Paper 5.5 with the source and target roles exchanged. -/
theorem ker_matrixCoefficient_eq_iff_span_eq_left
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    {x z y : H} (hx : x ≠ 0) (hz : z ≠ 0) (hy : y ≠ 0) :
    (matrixCoefficient pi x y).ker = (matrixCoefficient pi z y).ker ↔
      Submodule.span ℂ {x} = Submodule.span ℂ {z} := by
  rw [ker_matrixCoefficient_eq_iff_exists_ne_zero_smul_left pi hpi hx hy,
    span_singleton_eq_iff_exists_ne_zero_smul hz]

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
