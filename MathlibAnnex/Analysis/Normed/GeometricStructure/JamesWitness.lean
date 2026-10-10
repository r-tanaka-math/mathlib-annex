/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Orthogonality
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Support
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.Abel

/-!
# James's supporting-functional characterization

A contractive functional is constructed on the actual subspace spanned by
`x` and `y`, with values `‖x‖` and zero, and extended by Hahn-Banach. The
coefficient formula is proved independent of the chosen representation.
The proof includes zero seminorms and linearly dependent vectors; it needs
neither completeness nor a choice of basis or a closed-subspace quotient.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Orthogonality makes the value `a * ‖x‖` independent of a representation
`a • x + b • y`. This also holds when the seminorm of `x` vanishes. -/
theorem BirkhoffJamesOrthogonal.coefficient_eq {x y : E}
    (h : BirkhoffJamesOrthogonal 𝕜 x y) {a b c d : 𝕜}
    (habcd : a • x + b • y = c • x + d • y) :
    a * (‖x‖ : 𝕜) = c * (‖x‖ : 𝕜) := by
  have hz : (a - c) • x + (b - d) • y = 0 := by
    calc
      (a - c) • x + (b - d) • y =
          (a • x + b • y) - (c • x + d • y) := by
            simp only [sub_smul]
            abel
      _ = 0 := by rw [habcd, sub_self]
  have hle : ‖(a - c) * (‖x‖ : 𝕜)‖ ≤ 0 := by
    simpa only [hz, norm_zero, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x)] using h.norm_mul_le (a - c) (b - d)
  have hzero := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp (by simpa only [sub_mul] using hzero)

/-- The forward implication of James's characterization, with a closed-ball
norm bound. In particular, the zero vector requires no norm-one functional. -/
theorem BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero
    {x y : E} (h : BirkhoffJamesOrthogonal 𝕜 x y) :
    ∃ f ∈ normingFunctionals 𝕜 x, f y = 0 := by
  classical
  let p : Submodule 𝕜 E := Submodule.span 𝕜 ({x, y} : Set E)
  have hrep : ∀ z : p, ∃ a b : 𝕜, a • x + b • y = (z : E) := by
    intro z
    exact Submodule.mem_span_pair.mp z.property
  let a : p → 𝕜 := fun z => Classical.choose (hrep z)
  let b : p → 𝕜 := fun z => Classical.choose (Classical.choose_spec (hrep z))
  have hab (z : p) : a z • x + b z • y = (z : E) :=
    Classical.choose_spec (Classical.choose_spec (hrep z))
  have value_eq (z : p) (c d : 𝕜) (hz : c • x + d • y = (z : E)) :
      a z * (‖x‖ : 𝕜) = c * (‖x‖ : 𝕜) :=
    h.coefficient_eq 𝕜 ((hab z).trans hz.symm)
  let l : p →ₗ[𝕜] 𝕜 :=
    { toFun := fun z => a z * (‖x‖ : 𝕜)
      map_add' := by
        intro z w
        calc
          a (z + w) * (‖x‖ : 𝕜) = (a z + a w) * (‖x‖ : 𝕜) := by
            apply value_eq (z + w) (a z + a w) (b z + b w)
            change (a z + a w) • x + (b z + b w) • y = (z : E) + (w : E)
            calc
              _ = (a z • x + b z • y) + (a w • x + b w • y) := by
                simp only [add_smul]
                abel
              _ = _ := by rw [hab z, hab w]
          _ = a z * (‖x‖ : 𝕜) + a w * (‖x‖ : 𝕜) := add_mul _ _ _
      map_smul' := by
        intro c z
        change a (c • z) * (‖x‖ : 𝕜) = c * (a z * (‖x‖ : 𝕜))
        calc
          _ = (c * a z) * (‖x‖ : 𝕜) := by
            apply value_eq (c • z) (c * a z) (c * b z)
            change (c * a z) • x + (c * b z) • y = c • (z : E)
            rw [← smul_smul, ← smul_smul, ← smul_add, hab z]
          _ = _ := mul_assoc _ _ _ }
  have hl (z : p) : ‖l z‖ ≤ 1 * ‖z‖ := by
    change ‖a z * (‖x‖ : 𝕜)‖ ≤ 1 * ‖(z : E)‖
    simpa only [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x),
      one_mul, hab z] using h.norm_mul_le (a z) (b z)
  let g : StrongDual 𝕜 p := l.mkContinuous 1 hl
  have hg : ‖g‖ ≤ 1 := g.opNorm_le_bound zero_le_one hl
  obtain ⟨f, hf, hnorm⟩ := exists_extension_norm_eq p g
  have hx : x ∈ p := Submodule.subset_span (by simp)
  have hy : y ∈ p := Submodule.subset_span (by simp)
  have hfx : f x = (‖x‖ : 𝕜) := by
    calc
      f x = g ⟨x, hx⟩ := hf ⟨x, hx⟩
      _ = a ⟨x, hx⟩ * (‖x‖ : 𝕜) := rfl
      _ = 1 * (‖x‖ : 𝕜) := value_eq ⟨x, hx⟩ 1 0 (by simp)
      _ = (‖x‖ : 𝕜) := one_mul _
  have hfy : f y = 0 := by
    calc
      f y = g ⟨y, hy⟩ := hf ⟨y, hy⟩
      _ = a ⟨y, hy⟩ * (‖x‖ : 𝕜) := rfl
      _ = 0 * (‖x‖ : 𝕜) := value_eq ⟨y, hy⟩ 0 1 (by simp)
      _ = 0 := zero_mul _
  exact ⟨f, ⟨hnorm.trans_le hg, hfx⟩, hfy⟩

/-- A norming functional annihilating `y` witnesses Birkhoff-James orthogonality. -/
theorem birkhoffJamesOrthogonal_of_mem_normingFunctionals_apply_eq_zero
    {x y : E} {f : StrongDual 𝕜 E} (hf : f ∈ normingFunctionals 𝕜 x)
    (hy : f y = 0) : BirkhoffJamesOrthogonal 𝕜 x y := by
  intro a
  calc
    ‖x‖ = ‖f (x + a • y)‖ := by
      rw [map_add, map_smul, hy, smul_zero, add_zero, hf.2,
        RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖f‖ * ‖x + a • y‖ := f.le_opNorm _
    _ ≤ 1 * ‖x + a • y‖ :=
      mul_le_mul_of_nonneg_right hf.1 (norm_nonneg _)
    _ = ‖x + a • y‖ := one_mul _

/-- James's characterization over either scalar field, with both zero cases
and without a completeness assumption. -/
theorem birkhoffJamesOrthogonal_iff_exists_mem_normingFunctionals (x y : E) :
    BirkhoffJamesOrthogonal 𝕜 x y ↔ ∃ f ∈ normingFunctionals 𝕜 x, f y = 0 := by
  constructor
  · exact BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero 𝕜
  · rintro ⟨f, hf, hy⟩
    exact birkhoffJamesOrthogonal_of_mem_normingFunctionals_apply_eq_zero 𝕜 hf hy

end NormedSpace
