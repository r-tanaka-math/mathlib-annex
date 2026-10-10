/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarAbsoluteSupport
public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarSupport

/-!
# Common absolute supports as a weak-star extreme subset

The common set is exactly the intersection of the existing absolute norming
sets, now named on `WeakDual`. In particular, an empty primal set gives the
whole weak dual; boundedness assertions below require a nonempty primal set.

Absolute norming sets need not be convex. They are nevertheless `IsExtreme`
subsets of the dual ball: a normalized value-one support face detects the
endpoints of any segment through an absolute norming functional. This use of
`IsExtreme` does not assert convexity of those sets. Zero seminorms are handled
separately; completeness and a nontrivial primal space are not needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The intersection defining the common absolute supports, with the actual
weak-star topology. This is not a replacement for either existing support set. -/
def weakStarCommonAbsoluteNormingFunctionals (U : Set E) : Set (WeakDual 𝕜 E) :=
  ⋂ x ∈ U, weakStarAbsoluteNormingFunctionals 𝕜 x

@[simp]
theorem mem_weakStarCommonAbsoluteNormingFunctionals {U : Set E} {f : WeakDual 𝕜 E} :
    f ∈ weakStarCommonAbsoluteNormingFunctionals 𝕜 U ↔
      ∀ x ∈ U, f.toStrongDual ∈ absoluteNormingFunctionals 𝕜 x := by
  simp only [weakStarCommonAbsoluteNormingFunctionals, mem_iInter,
    weakStarAbsoluteNormingFunctionals, mem_preimage]

@[simp]
theorem weakStarCommonAbsoluteNormingFunctionals_empty :
    weakStarCommonAbsoluteNormingFunctionals 𝕜 (∅ : Set E) = univ := by
  ext f
  constructor
  · intro _
    exact mem_univ f
  · intro _
    apply (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr
    intro x hx
    exact False.elim hx

theorem isClosed_weakStarCommonAbsoluteNormingFunctionals (U : Set E) :
    IsClosed (weakStarCommonAbsoluteNormingFunctionals 𝕜 U) :=
  isClosed_biInter fun x _ => isClosed_weakStarAbsoluteNormingFunctionals 𝕜 x

theorem weakStarCommonAbsoluteNormingFunctionals_subset_closedBall {U : Set E}
    (hne : U.Nonempty) :
    weakStarCommonAbsoluteNormingFunctionals 𝕜 U ⊆
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 := by
  obtain ⟨x, hx⟩ := hne
  intro f hf
  exact mem_closedBall_zero_iff.mpr
    (((mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mp hf x hx).1)

theorem isCompact_weakStarCommonAbsoluteNormingFunctionals {U : Set E}
    (hne : U.Nonempty) : IsCompact (weakStarCommonAbsoluteNormingFunctionals 𝕜 U) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1).of_isClosed_subset
    (isClosed_weakStarCommonAbsoluteNormingFunctionals 𝕜 U)
    (weakStarCommonAbsoluteNormingFunctionals_subset_closedBall 𝕜 hne)

/-- The earlier simultaneous-support theorem gives nonemptiness of the named
weak-star intersection. No new support or phase choices are postulated. -/
theorem IsBirkhoffJamesFilter.nonempty_weakStarCommonAbsoluteNormingFunctionals
    {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U) :
    (weakStarCommonAbsoluteNormingFunctionals 𝕜 U).Nonempty := by
  obtain ⟨f, hf⟩ := hU.exists_common_absoluteNormingFunctional 𝕜
  exact ⟨f.toWeakDual, (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr hf⟩

/-- Absolute norming functionals form an extreme subset of the dual ball,
although they generally do not form a convex set. -/
theorem isExtreme_weakStarAbsoluteNormingFunctionals (x : E) :
    IsExtreme ℝ (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)
      (weakStarAbsoluteNormingFunctionals 𝕜 x) := by
  refine ⟨fun _ hf => mem_closedBall_zero_iff.mpr hf.1, ?_⟩
  intro g hg h hh f hf hseg
  have hgnorm : ‖g.toStrongDual‖ ≤ 1 := mem_closedBall_zero_iff.mp hg
  refine ⟨hgnorm, ?_⟩
  change ‖g x‖ = ‖x‖
  have hfnorm : ‖f x‖ = ‖x‖ := hf.2
  by_cases hx : ‖x‖ = 0
  · have hbound := g.toStrongDual.le_opNorm x
    change ‖g x‖ ≤ ‖g.toStrongDual‖ * ‖x‖ at hbound
    have hzero : ‖g x‖ = 0 := le_antisymm
      (by simpa only [hx, mul_zero] using hbound) (norm_nonneg _)
    exact hzero.trans hx.symm
  · have hfx : f x ≠ 0 := norm_ne_zero_iff.mp (hf.2.trans_ne hx)
    let z : E := (f x)⁻¹ • x
    have hzball : z ∈ closedBall (0 : E) 1 := by
      apply mem_closedBall_zero_iff.mpr
      simp only [z, norm_smul, norm_inv, hfnorm, inv_mul_cancel₀ hx, le_refl]
    have hfz : f ∈ weakStarSupportFunctionals 𝕜 ({z} : Set E) := by
      refine ⟨hf.1, ?_⟩
      rintro y rfl
      change f.toStrongDual ((f x)⁻¹ • x) = 1
      rw [map_smul, smul_eq_mul]
      change (f x)⁻¹ * f x = 1
      exact inv_mul_cancel₀ hfx
    have hface := isExtreme_weakStarSupportFunctionals 𝕜
      (show ({z} : Set E) ⊆ closedBall (0 : E) 1 from
        singleton_subset_iff.mpr hzball)
    have hgz := hface.2 hg hh hfz hseg
    have hvalue : (f x)⁻¹ * g x = 1 := by
      have hv := hgz.2 z (mem_singleton z)
      change g.toStrongDual ((f x)⁻¹ • x) = 1 at hv
      rw [map_smul, smul_eq_mul] at hv
      change (f x)⁻¹ * g x = 1 at hv
      exact hv
    have heq : g x = f x := by
      calc
        g x = f x * ((f x)⁻¹ * g x) := by
          rw [← mul_assoc, mul_inv_cancel₀ hfx, one_mul]
        _ = f x := by rw [hvalue, mul_one]
    rw [heq, hfnorm]

/-- The common absolute-support set is an extreme subset, not necessarily a
convex face, of the weak-star dual ball. -/
theorem isExtreme_weakStarCommonAbsoluteNormingFunctionals {U : Set E}
    (hne : U.Nonempty) :
    IsExtreme ℝ (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)
      (weakStarCommonAbsoluteNormingFunctionals 𝕜 U) := by
  refine ⟨weakStarCommonAbsoluteNormingFunctionals_subset_closedBall 𝕜 hne, ?_⟩
  intro f hf g hg z hz hseg
  apply (mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mpr
  intro x hx
  exact (isExtreme_weakStarAbsoluteNormingFunctionals 𝕜 x).2 hf hg
    ((mem_weakStarCommonAbsoluteNormingFunctionals 𝕜).mp hz x hx) hseg

end NormedSpace
