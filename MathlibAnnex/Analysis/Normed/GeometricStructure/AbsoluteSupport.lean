/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.JamesWitness
public import Mathlib.Tactic.Linarith

/-!
# Right orthogonality sets and absolute norming functionals

The preorder is inclusion of right orthogonality sets. It is provided as an
explicit structure, not as a global order instance on the vector space.
Absolute norming functionals are used only as an auxiliary set; the existing
`normingFunctionals` and face definition of the geometric structure space are
unchanged. The characterization of the preorder includes zero seminorms.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The right Birkhoff-James orthogonality set of a vector. -/
def birkhoffJamesOrthogonalSet (x : E) : Set E :=
  {y | BirkhoffJamesOrthogonal 𝕜 x y}

@[simp]
theorem mem_birkhoffJamesOrthogonalSet {x y : E} :
    y ∈ birkhoffJamesOrthogonalSet 𝕜 x ↔ BirkhoffJamesOrthogonal 𝕜 x y :=
  Iff.rfl

/-- The preorder used in the filter presentation of geometric structure spaces.
It is deliberately not registered as an order instance on `E`. -/
def birkhoffJamesPreorder : Preorder E where
  le x y := birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hxy hyz := Set.Subset.trans hxy hyz

/-- Contractive functionals attaining the norm in absolute value. -/
def absoluteNormingFunctionals (x : E) : Set (StrongDual 𝕜 E) :=
  {f | ‖f‖ ≤ 1 ∧ ‖f x‖ = ‖x‖}

@[simp]
theorem mem_absoluteNormingFunctionals {x : E} {f : StrongDual 𝕜 E} :
    f ∈ absoluteNormingFunctionals 𝕜 x ↔ ‖f‖ ≤ 1 ∧ ‖f x‖ = ‖x‖ :=
  Iff.rfl

theorem normingFunctionals_subset_absoluteNormingFunctionals (x : E) :
    normingFunctionals 𝕜 x ⊆ absoluteNormingFunctionals 𝕜 x := by
  intro f hf
  refine ⟨hf.1, ?_⟩
  rw [hf.2, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]

theorem nonempty_absoluteNormingFunctionals (x : E) :
    (absoluteNormingFunctionals 𝕜 x).Nonempty := by
  obtain ⟨f, hf⟩ := nonempty_normingFunctionals 𝕜 x
  exact ⟨f, normingFunctionals_subset_absoluteNormingFunctionals 𝕜 x hf⟩

/-- Absolute norm attainment suffices for the easy direction of James's theorem;
no choice of phase is needed in this direction. -/
theorem birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero
    {x y : E} {f : StrongDual 𝕜 E} (hf : f ∈ absoluteNormingFunctionals 𝕜 x)
    (hy : f y = 0) : BirkhoffJamesOrthogonal 𝕜 x y := by
  intro a
  calc
    ‖x‖ = ‖f (x + a • y)‖ := by
      rw [map_add, map_smul, hy, smul_zero, add_zero, hf.2]
    _ ≤ ‖f‖ * ‖x + a • y‖ := f.le_opNorm _
    _ ≤ 1 * ‖x + a • y‖ := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg _)
    _ = ‖x + a • y‖ := one_mul _

theorem mem_birkhoffJamesOrthogonalSet_iff_exists_absoluteNormingFunctional
    (x y : E) :
    y ∈ birkhoffJamesOrthogonalSet 𝕜 x ↔
      ∃ f ∈ absoluteNormingFunctionals 𝕜 x, f y = 0 := by
  constructor
  · intro h
    obtain ⟨f, hf, hy⟩ := BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero 𝕜 h
    exact ⟨f, normingFunctionals_subset_absoluteNormingFunctionals 𝕜 x hf, hy⟩
  · rintro ⟨f, hf, hy⟩
    exact birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero 𝕜 hf hy

/-- Inclusion of orthogonality sets is exactly inclusion of absolute norming
sets. The proof avoids division by a functional value and handles zero
seminorms before cancellation. -/
theorem birkhoffJamesOrthogonalSet_subset_iff {x y : E} :
    birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y ↔
      absoluteNormingFunctionals 𝕜 x ⊆ absoluteNormingFunctionals 𝕜 y := by
  constructor
  · intro h f hf
    have bound (z : E) : ‖f z‖ ≤ ‖z‖ := by
      calc
        ‖f z‖ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
        _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg z)
        _ = ‖z‖ := one_mul _
    refine ⟨hf.1, ?_⟩
    by_cases hx : ‖x‖ = 0
    · have hy : ‖y‖ = 0 :=
        (birkhoffJamesOrthogonal_self_iff_norm_eq_zero y).mp
          (h (birkhoffJamesOrthogonal_of_norm_eq_zero hx))
      exact le_antisymm (bound y) (by rw [hy]; exact norm_nonneg _)
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
      let z : E := (f y) • x - (f x) • y
      have hfz : f z = 0 := by
        simp only [z, map_sub, map_smul, smul_eq_mul, mul_comm (f y) (f x), sub_self]
      have hyz : BirkhoffJamesOrthogonal 𝕜 y z := h
        (birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero 𝕜 hf hfz)
      obtain ⟨g, hg, hgz⟩ := hyz.exists_mem_normingFunctionals_apply_eq_zero 𝕜
      have heq : (f y) * (g x) = (f x) * (‖y‖ : 𝕜) := by
        have hz' : (f y) * (g x) - (f x) * (g y) = 0 := by
          simpa only [z, map_sub, map_smul, smul_eq_mul] using hgz
        simpa only [hg.2] using sub_eq_zero.mp hz'
      have heqnorm : ‖f y‖ * ‖g x‖ = ‖x‖ * ‖y‖ := by
        simpa only [norm_mul, hf.2, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg y)] using congrArg norm heq
      have hgx : ‖g x‖ ≤ ‖x‖ := by
        calc
          ‖g x‖ ≤ ‖g‖ * ‖x‖ := g.le_opNorm x
          _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hg.1 (norm_nonneg x)
          _ = ‖x‖ := one_mul _
      have hprod := mul_le_mul_of_nonneg_left hgx (norm_nonneg (f y))
      have hmul : ‖x‖ * ‖y‖ ≤ ‖x‖ * ‖f y‖ := by
        calc
          _ = ‖f y‖ * ‖g x‖ := heqnorm.symm
          _ ≤ ‖f y‖ * ‖x‖ := hprod
          _ = _ := mul_comm _ _
      exact le_antisymm (bound y) ((mul_le_mul_iff_right₀ hxpos).mp hmul)
  · intro h z hz
    obtain ⟨f, hf, hfz⟩ := BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero 𝕜 hz
    exact birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero 𝕜
      (h (normingFunctionals_subset_absoluteNormingFunctionals 𝕜 x hf)) hfz

theorem birkhoffJamesOrthogonalSet_subset_smul (x : E) (a : 𝕜) :
    birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 (a • x) := by
  intro y hy
  change BirkhoffJamesOrthogonal 𝕜 (a • x) y
  simpa only [one_smul] using hy.smul a 1

theorem birkhoffJamesOrthogonalSet_smul {a : 𝕜} (ha : a ≠ 0) (x : E) :
    birkhoffJamesOrthogonalSet 𝕜 (a • x) = birkhoffJamesOrthogonalSet 𝕜 x := by
  apply Set.Subset.antisymm
  · intro y hy
    change BirkhoffJamesOrthogonal 𝕜 x y
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hy.smul a⁻¹ 1
  · exact birkhoffJamesOrthogonalSet_subset_smul 𝕜 x a

@[simp]
theorem birkhoffJamesOrthogonalSet_zero :
    birkhoffJamesOrthogonalSet 𝕜 (0 : E) = Set.univ := by
  ext y
  simp [birkhoffJamesOrthogonalSet]

end NormedSpace
