/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.PreorderFilter
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Compactness.Compact

/-!
# Common absolute supports by weak-star compactness

All compactness and closedness statements are on `WeakDual`. Cantor's
intersection theorem supplies a single functional, including an additional
weak-star closed constraint, from the downward-directed family. This is not
an exchange of universal and existential quantifiers without compactness.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Absolute norming functionals as a subset of the weak-star dual. -/
def weakStarAbsoluteNormingFunctionals (x : E) : Set (WeakDual 𝕜 E) :=
  WeakDual.toStrongDual ⁻¹' absoluteNormingFunctionals 𝕜 x

@[simp]
theorem mem_weakStarAbsoluteNormingFunctionals {x : E} {f : WeakDual 𝕜 E} :
    f ∈ weakStarAbsoluteNormingFunctionals 𝕜 x ↔
      ‖f.toStrongDual‖ ≤ 1 ∧ ‖f x‖ = ‖x‖ := Iff.rfl

theorem weakStarAbsoluteNormingFunctionals_eq_inter (x : E) :
    weakStarAbsoluteNormingFunctionals 𝕜 x =
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1) ∩
        {f : WeakDual 𝕜 E | ‖f x‖ = ‖x‖} := by
  ext f
  simp only [mem_weakStarAbsoluteNormingFunctionals, mem_inter_iff, mem_preimage,
    mem_closedBall_zero_iff, mem_setOf_eq]

theorem isClosed_weakStarAbsoluteNormingFunctionals (x : E) :
    IsClosed (weakStarAbsoluteNormingFunctionals 𝕜 x) := by
  rw [weakStarAbsoluteNormingFunctionals_eq_inter]
  exact (WeakDual.isClosed_closedBall (0 : StrongDual 𝕜 E) 1).inter
    (isClosed_eq (WeakDual.eval_continuous x).norm continuous_const)

theorem isCompact_weakStarAbsoluteNormingFunctionals (x : E) :
    IsCompact (weakStarAbsoluteNormingFunctionals 𝕜 x) := by
  letI : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
  exact (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) 1).of_isClosed_subset
    (isClosed_weakStarAbsoluteNormingFunctionals 𝕜 x)
    (fun _ hf => mem_closedBall_zero_iff.mpr hf.1)

/-- A downward-directed nonempty primal subset admits simultaneous absolute
supports satisfying any weak-star closed constraint which is feasible at
its individual points. -/
theorem exists_common_absoluteNormingFunctional_of_isClosed {U : Set E} (hne : U.Nonempty)
    (hdir : ∀ x ∈ U, ∀ y ∈ U, ∃ z ∈ U,
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y)
    {C : Set (WeakDual 𝕜 E)} (hC : IsClosed C)
    (hfeas : ∀ x ∈ U, (weakStarAbsoluteNormingFunctionals 𝕜 x ∩ C).Nonempty) :
    ∃ f : StrongDual 𝕜 E, (∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) ∧
      f.toWeakDual ∈ C := by
  letI : Nonempty U := hne.to_subtype
  let t : U → Set (WeakDual 𝕜 E) := fun x => weakStarAbsoluteNormingFunctionals 𝕜 x.val ∩ C
  have htd : Directed (· ⊇ ·) t := by
    intro x y
    obtain ⟨z, hz, hzx, hzy⟩ := hdir x.val x.property y.val y.property
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · intro f hf
      exact ⟨(birkhoffJamesOrthogonalSet_subset_iff 𝕜).mp hzx hf.1, hf.2⟩
    · intro f hf
      exact ⟨(birkhoffJamesOrthogonalSet_subset_iff 𝕜).mp hzy hf.1, hf.2⟩
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd
    (fun x => hfeas x.val x.property)
    (fun x => (isCompact_weakStarAbsoluteNormingFunctionals 𝕜 x.val).inter_right hC)
    (fun x => (isClosed_weakStarAbsoluteNormingFunctionals 𝕜 x.val).inter hC)
  refine ⟨f.toStrongDual, fun x hx => (mem_iInter.mp hf ⟨x, hx⟩).1, ?_⟩
  obtain ⟨x, hx⟩ := hne
  exact (mem_iInter.mp hf ⟨x, hx⟩).2

theorem IsBirkhoffJamesFilter.exists_common_absoluteNormingFunctional {U : Set E}
    (hU : IsBirkhoffJamesFilter 𝕜 U) :
    ∃ f : StrongDual 𝕜 E, ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x := by
  obtain ⟨f, hf, _⟩ := exists_common_absoluteNormingFunctional_of_isClosed 𝕜
    (hU.nonempty 𝕜) (fun _ hx _ hy => hU.directed 𝕜 hx hy) isClosed_univ (by
      intro x _
      obtain ⟨f, hf⟩ := nonempty_absoluteNormingFunctionals 𝕜 x
      exact ⟨f.toWeakDual, hf, mem_univ _⟩)
  exact ⟨f, hf⟩

/-- One common absolute support can be chosen to annihilate a given member
of the intersection kernel. This theorem applies to any nonempty downward
directed set, not just to an upward-closed filter. -/
theorem mem_birkhoffJamesKernel_iff_exists_common_absoluteNormingFunctional
    {U : Set E} (hne : U.Nonempty)
    (hdir : ∀ x ∈ U, ∀ y ∈ U, ∃ z ∈ U,
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y) (y : E) :
    y ∈ birkhoffJamesKernel 𝕜 U ↔
      ∃ f : StrongDual 𝕜 E, (∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) ∧ f y = 0 := by
  constructor
  · intro hy
    exact exists_common_absoluteNormingFunctional_of_isClosed 𝕜 hne hdir
      (isClosed_eq (WeakDual.eval_continuous y) continuous_const) (by
        intro x hx
        obtain ⟨f, hf, hfy⟩ :=
          BirkhoffJamesOrthogonal.exists_mem_normingFunctionals_apply_eq_zero 𝕜 (hy x hx)
        exact ⟨f.toWeakDual, normingFunctionals_subset_absoluteNormingFunctionals 𝕜 x hf, hfy⟩)
  · rintro ⟨f, hf, hfy⟩ x hx
    exact birkhoffJamesOrthogonal_of_mem_absoluteNormingFunctionals_apply_eq_zero 𝕜
      (hf x hx) hfy

end NormedSpace
