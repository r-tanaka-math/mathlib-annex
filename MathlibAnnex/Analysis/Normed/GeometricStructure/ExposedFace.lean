/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.CommonSupport
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Face
public import Mathlib.Analysis.Convex.Exposed

public import Mathlib.Tactic.Ring

/-!
# Proper faces of the unit ball and their supporting hyperplanes

A proper extreme subset of the ball misses its interior: an interior point
first forces zero into the face, and zero then forces every point of the ball.
For maximal faces, common support and maximality identify the face with every
one of its supporting slices. Complex slices are exposed by real parts.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

section Real

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An extreme subset of the unit ball containing zero is the whole ball. -/
theorem eq_closedBall_of_isExtreme_of_zero_mem {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0 : E) 1) F) (hzero : 0 ∈ F) :
    F = closedBall (0 : E) 1 := by
  refine Set.Subset.antisymm hF.subset ?_
  intro x hx
  have hneg : -x ∈ closedBall (0 : E) 1 := by
    simpa only [mem_closedBall_zero_iff, norm_neg] using hx
  apply hF.left_mem_of_mem_openSegment hx hneg hzero
  refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [smul_neg, add_neg_cancel]

/-- An extreme subset meeting the open unit ball is the whole closed unit ball. -/
theorem eq_closedBall_of_isExtreme_of_norm_lt_one {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0 : E) 1) F)
    {x : E} (hx : x ∈ F) (hxnorm : ‖x‖ < 1) : F = closedBall (0 : E) 1 := by
  let a : ℝ := (1 + ‖x‖) / 2
  have ha : 0 < a := by dsimp [a]; linarith [norm_nonneg x]
  have haone : a < 1 := by dsimp [a]; linarith
  have hxa : ‖x‖ ≤ a := by dsimp [a]; linarith
  have hy : a⁻¹ • x ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 ha)]
    calc
      a⁻¹ * ‖x‖ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hxa (inv_nonneg.2 ha.le)
      _ = 1 := inv_mul_cancel₀ ha.ne'
  apply eq_closedBall_of_isExtreme_of_zero_mem hF
  apply hF.left_mem_of_mem_openSegment (mem_closedBall_self zero_le_one) hy hx
  refine ⟨1 - a, a, sub_pos.2 haone, ha, by ring, ?_⟩
  simp only [smul_zero, zero_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- A proper extreme subset of the ball lies on the sphere. Convexity is not
needed for this implication. -/
theorem subset_sphere_of_isExtreme_of_ne_closedBall {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0 : E) 1) F) (hne : F ≠ closedBall (0 : E) 1) :
    F ⊆ sphere (0 : E) 1 := by
  intro x hx
  rw [mem_sphere, dist_zero_right]
  have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hF.subset hx)
  by_contra hneq
  have hlt : ‖x‖ < 1 := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact (hneq heq).elim
  exact hne (eq_closedBall_of_isExtreme_of_norm_lt_one hF hx hlt)

theorem IsMaximalFace.subset_sphere {F : Set E} (hF : IsMaximalFace F) :
    F ⊆ sphere (0 : E) 1 :=
  subset_sphere_of_isExtreme_of_ne_closedBall hF.isExtreme hF.ne_closedBall

end Real

section RCLike

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The unit-ball slice where a continuous functional takes the value one.
It need not be nonempty, and its definition makes no maximality claim. -/
def unitBallSupportFace (f : StrongDual 𝕜 E) : Set E :=
  closedBall (0 : E) 1 ∩ {x | f x = 1}

@[simp]
theorem mem_unitBallSupportFace (f : StrongDual 𝕜 E) (x : E) :
    x ∈ unitBallSupportFace 𝕜 f ↔ x ∈ closedBall (0 : E) 1 ∧ f x = 1 := Iff.rfl

theorem isClosed_unitBallSupportFace (f : StrongDual 𝕜 E) :
    IsClosed (unitBallSupportFace 𝕜 f) :=
  isClosed_closedBall.inter (isClosed_eq f.continuous continuous_const)

theorem unitBallSupportFace_ne_closedBall (f : StrongDual 𝕜 E) :
    unitBallSupportFace 𝕜 f ≠ closedBall (0 : E) 1 := by
  intro h
  have hzero : 0 ∈ unitBallSupportFace 𝕜 f := by
    rw [h]
    exact mem_closedBall_self zero_le_one
  have hval : f 0 = 1 := hzero.2
  have h01 : (0 : 𝕜) = 1 := by simpa only [map_zero] using hval
  exact zero_ne_one h01

theorem unitBallSupportFace_subset_sphere {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) :
    unitBallSupportFace 𝕜 f ⊆ sphere (0 : E) 1 := by
  intro x hx
  rw [mem_sphere, dist_zero_right]
  refine le_antisymm (mem_closedBall_zero_iff.1 hx.1) ?_
  calc
    1 = ‖f x‖ := by rw [hx.2, norm_one]
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg x)
    _ = ‖x‖ := one_mul _

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

theorem convex_unitBallSupportFace (f : StrongDual 𝕜 E) :
    Convex ℝ (unitBallSupportFace 𝕜 f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_closedBall (0 : E) 1) hx.1 hy.1 ha hb hab, ?_⟩
  change (f.restrictScalars ℝ) (a • x + b • y) = 1
  rw [map_add, map_smul, map_smul]
  change a • f x + b • f y = 1
  rw [hx.2, hy.2, ← add_smul, hab, one_smul]

/-- A contractive complex functional exposes its nonempty slice by its real
part. The statement also covers the empty slice, as does Mathlib's IsExposed. -/
theorem isExposed_unitBallSupportFace {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) :
    IsExposed ℝ (closedBall (0 : E) 1) (unitBallSupportFace 𝕜 f) := by
  rintro ⟨x₀, hx₀⟩
  let l : StrongDual ℝ E := RCLike.reCLM.comp (f.restrictScalars ℝ)
  have hbound : ∀ x ∈ closedBall (0 : E) 1, ‖f x‖ ≤ 1 := by
    intro x hx
    simpa only [one_mul] using f.le_of_opNorm_le_of_le hf (mem_closedBall_zero_iff.1 hx)
  have hl : ∀ x ∈ closedBall (0 : E) 1, l x ≤ 1 :=
    fun x hx => (RCLike.re_le_norm (f x)).trans (hbound x hx)
  have hl₀ : l x₀ = 1 := by
    change RCLike.re (f x₀) = 1
    rw [hx₀.2, RCLike.one_re]
  refine ⟨l, Set.ext fun x => ?_⟩
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hlx : l x = 1 := by
      change RCLike.re (f x) = 1
      rw [hx.2, RCLike.one_re]
    intro y hy
    rw [hlx]
    exact hl y hy
  · rintro ⟨hx, hmax⟩
    have hre : RCLike.re (f x) = 1 :=
      le_antisymm (hl x hx) (hl₀ ▸ hmax x₀ hx₀.1)
    refine ⟨hx, ?_⟩
    have h := RCLike.re_eq_self_of_le (a := f x) ((hbound x hx).trans hre.ge)
    change f x = 1
    simpa only [hre, algebraMap.coe_one] using h.symm

theorem isExtreme_unitBallSupportFace {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) :
    IsExtreme ℝ (closedBall (0 : E) 1) (unitBallSupportFace 𝕜 f) :=
  (isExposed_unitBallSupportFace 𝕜 hf).isExtreme

theorem IsMaximalFace.nonempty_supportFunctionals {F : Set E} (hF : IsMaximalFace F) :
    (supportFunctionals 𝕜 F).Nonempty :=
  nonempty_supportFunctionals_of_convex_subset_sphere 𝕜 hF.nonempty hF.convex hF.subset_sphere

/-- Every supporting functional of a maximal face exposes that same face. -/
theorem IsMaximalFace.eq_unitBallSupportFace {F : Set E} (hF : IsMaximalFace F)
    {f : StrongDual 𝕜 E} (hf : f ∈ supportFunctionals 𝕜 F) :
    F = unitBallSupportFace 𝕜 f := by
  symm
  exact hF.maximal (unitBallSupportFace 𝕜 f)
    (fun x hx => ⟨hF.subset_closedBall hx, hf.2 x hx⟩)
    (convex_unitBallSupportFace 𝕜 f) (isExtreme_unitBallSupportFace 𝕜 hf.1)
    (unitBallSupportFace_ne_closedBall 𝕜 f)

end RCLike

section RealClosedness

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsMaximalFace.isExposed {F : Set E} (hF : IsMaximalFace F) :
    IsExposed ℝ (closedBall (0 : E) 1) F := by
  obtain ⟨f, hf⟩ := hF.nonempty_supportFunctionals ℝ
  rw [hF.eq_unitBallSupportFace ℝ hf]
  exact isExposed_unitBallSupportFace ℝ hf.1

/-- A maximal proper face is norm-closed, even in an incomplete space. -/
theorem IsMaximalFace.isClosed {F : Set E} (hF : IsMaximalFace F) : IsClosed F :=
  hF.isExposed.isClosed isClosed_closedBall

end RealClosedness

end NormedSpace
