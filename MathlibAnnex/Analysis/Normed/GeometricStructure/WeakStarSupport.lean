/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Support
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Convex.Extreme

public import Mathlib.Tactic.Linarith

/-!
# Weak-star realization of support families

The carrier is the preimage of `supportFunctionals` under the canonical linear
identity `WeakDual.toStrongDual`. Every topological statement in this file is
made on `WeakDual`, never on the norm-topologized `StrongDual`.

Closedness follows from weak-star closedness of the dual ball and continuity
of evaluations. Compactness uses Banach-Alaoglu. Faciality uses real parts and
the equality case for a scalar of norm at most one. Neither convexity nor
nonemptiness of the primal subset is required for the faciality assertion;
only containment in the primal closed unit ball is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The existing support family, now equipped with the weak-star topology
through the canonical identification of the two dual types. -/
def weakStarSupportFunctionals (F : Set E) : Set (WeakDual 𝕜 E) :=
  WeakDual.toStrongDual ⁻¹' supportFunctionals 𝕜 F

@[simp]
theorem mem_weakStarSupportFunctionals (F : Set E) (f : WeakDual 𝕜 E) :
    f ∈ weakStarSupportFunctionals 𝕜 F ↔
      ‖f.toStrongDual‖ ≤ 1 ∧ ∀ x ∈ F, f x = 1 := Iff.rfl

/-- The weak-star carrier is exactly the image of the original carrier,
not a closure or completion of it. -/
theorem image_toWeakDual_supportFunctionals (F : Set E) :
    StrongDual.toWeakDual '' supportFunctionals 𝕜 F = weakStarSupportFunctionals 𝕜 F := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hf
    exact ⟨f.toStrongDual, hf, rfl⟩

theorem image_toStrongDual_weakStarSupportFunctionals (F : Set E) :
    WeakDual.toStrongDual '' weakStarSupportFunctionals 𝕜 F = supportFunctionals 𝕜 F := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hf
    exact ⟨f.toWeakDual, hf, rfl⟩

theorem nonempty_weakStarSupportFunctionals_iff (F : Set E) :
    (weakStarSupportFunctionals 𝕜 F).Nonempty ↔ (supportFunctionals 𝕜 F).Nonempty := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toStrongDual, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.toWeakDual, hf⟩

theorem weakStarSupportFunctionals_eq_inter_iInter (F : Set E) :
    weakStarSupportFunctionals 𝕜 F =
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) ∩
        ⋂ x ∈ F, {f : WeakDual 𝕜 E | f x = 1} := by
  ext f
  simp only [mem_weakStarSupportFunctionals, mem_inter_iff, mem_preimage,
    mem_closedBall_zero_iff, mem_iInter, mem_setOf_eq]

theorem weakStarSupportFunctionals_subset_closedBall (F : Set E) :
    weakStarSupportFunctionals 𝕜 F ⊆
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 :=
  fun _ hf => mem_closedBall_zero_iff.2 hf.1

/-- The supporting family is weak-star closed, for every primal set. -/
theorem isClosed_weakStarSupportFunctionals (F : Set E) :
    IsClosed (weakStarSupportFunctionals 𝕜 F) := by
  rw [weakStarSupportFunctionals_eq_inter_iInter]
  refine (WeakDual.isClosed_closedBall (0 : StrongDual 𝕜 E) 1).inter ?_
  exact isClosed_biInter fun x _ =>
    isClosed_eq (WeakDual.eval_continuous x) continuous_const

/-- Banach-Alaoglu makes the support family weak-star compact. The primal
space need not be complete, and the support family may be empty. -/
theorem isCompact_weakStarSupportFunctionals (F : Set E) :
    IsCompact (weakStarSupportFunctionals 𝕜 F) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1).of_isClosed_subset
    (isClosed_weakStarSupportFunctionals 𝕜 F)
    (weakStarSupportFunctionals_subset_closedBall 𝕜 F)

/-- The weak-star support family is real-convex. -/
theorem convex_weakStarSupportFunctionals (F : Set E) :
    Convex ℝ (weakStarSupportFunctionals 𝕜 F) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_⟩
  · change ‖a • f.toStrongDual + b • g.toStrongDual‖ ≤ 1
    exact mem_closedBall_zero_iff.1
      ((convex_closedBall (0 : StrongDual 𝕜 E) 1)
        (mem_closedBall_zero_iff.2 hf.1) (mem_closedBall_zero_iff.2 hg.1) ha hb hab)
  · intro x hx
    change a • f x + b • g x = 1
    have hfx := hf.2 x hx
    have hgx := hg.2 x hx
    change f x = 1 at hfx
    change g x = 1 at hgx
    rw [hfx, hgx, ← add_smul, hab, one_smul]

/-- A support family over a subset of the primal ball is an extreme subset
of the weak-star dual ball. Convexity of the primal set is not needed. -/
theorem isExtreme_weakStarSupportFunctionals {F : Set E}
    (hF : F ⊆ closedBall (0 : E) 1) :
    IsExtreme ℝ (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)
      (weakStarSupportFunctionals 𝕜 F) := by
  refine ⟨weakStarSupportFunctionals_subset_closedBall 𝕜 F, ?_⟩
  intro f hf g hg z hz hzseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hzseg
  refine ⟨mem_closedBall_zero_iff.1 hf, ?_⟩
  intro x hx
  have hfx : ‖f x‖ ≤ 1 := by
    change ‖f.toStrongDual x‖ ≤ 1
    simpa only [one_mul] using f.toStrongDual.le_of_opNorm_le_of_le
      (mem_closedBall_zero_iff.1 hf) (mem_closedBall_zero_iff.1 (hF hx))
  have hgx : ‖g x‖ ≤ 1 := by
    change ‖g.toStrongDual x‖ ≤ 1
    simpa only [one_mul] using g.toStrongDual.le_of_opNorm_le_of_le
      (mem_closedBall_zero_iff.1 hg) (mem_closedBall_zero_iff.1 (hF hx))
  have hval : a • f x + b • g x = 1 := by
    calc
      a • f x + b • g x = (a • f + b • g) x := rfl
      _ = z x := congrArg (fun w : WeakDual 𝕜 E => w x) heq
      _ = 1 := hz.2 x hx
  have hreval : a * RCLike.re (f x) + b * RCLike.re (g x) = 1 := by
    have h := congrArg (fun w : 𝕜 => (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) w) hval
    simpa only [map_add, map_smul, smul_eq_mul, RCLike.reCLM_apply,
      RCLike.one_re] using h
  have hrf : RCLike.re (f x) ≤ 1 := (RCLike.re_le_norm (f x)).trans hfx
  have hrg : RCLike.re (g x) ≤ 1 := (RCLike.re_le_norm (g x)).trans hgx
  have hrfone : RCLike.re (f x) = 1 := by
    have hnonneg : 0 ≤ b * (1 - RCLike.re (g x)) :=
      mul_nonneg hb.le (sub_nonneg.2 hrg)
    have hle : a * 1 ≤ a * RCLike.re (f x) := by
      nlinarith only [hab, hreval, hnonneg]
    exact le_antisymm hrf ((mul_le_mul_iff_right₀ ha).1 hle)
  have h := RCLike.re_eq_self_of_le (a := f x) (hfx.trans hrfone.ge)
  change f x = 1
  simpa only [hrfone, algebraMap.coe_one] using h.symm

theorem weakStarSupportFunctionals_ne_closedBall {F : Set E} (hne : F.Nonempty) :
    weakStarSupportFunctionals 𝕜 F ≠
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 := by
  intro heq
  have hz : (0 : WeakDual 𝕜 E) ∈ weakStarSupportFunctionals 𝕜 F := by
    rw [heq]
    exact mem_closedBall_zero_iff.2 (by simp)
  obtain ⟨x, hx⟩ := hne
  have h01 : (0 : 𝕜) = 1 := hz.2 x hx
  exact zero_ne_one h01

theorem norm_toStrongDual_eq_one_of_mem_weakStarSupportFunctionals
    {F : Set E} (hne : F.Nonempty) (hF : F ⊆ closedBall (0 : E) 1)
    {f : WeakDual 𝕜 E} (hf : f ∈ weakStarSupportFunctionals 𝕜 F) :
    ‖f.toStrongDual‖ = 1 :=
  norm_eq_one_of_mem_supportFunctionals 𝕜 hne
    (fun x hx => mem_closedBall_zero_iff.1 (hF hx)) hf

end NormedSpace
