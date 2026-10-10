/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.ExposedFace
public import Mathlib.Order.Zorn

/-!
# Existence of maximal proper faces

Maximal proper convex faces are precisely the nonempty maximal convex subsets
of the unit sphere. Zorn is applied to sphere subsets; an increasing-chain
union remains on the sphere. Common support subsequently proves faciality.
There is no compactness or completeness assumption on the primal space.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u

namespace NormedSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A maximal proper face is maximal among all real-convex sphere subsets,
not merely among those already known to be faces. -/
theorem IsMaximalFace.maximal_convex_subset_sphere {F : Set E} (hF : IsMaximalFace F) :
    Maximal (fun G : Set E => Convex ℝ G ∧ G ⊆ sphere (0 : E) 1) F := by
  refine ⟨⟨hF.convex, hF.subset_sphere⟩, ?_⟩
  intro G hG hFG
  obtain ⟨x₀, hx₀⟩ := hF.nonempty
  obtain ⟨f, hfnorm, hfG⟩ := exists_dual_eq_one_of_convex_subset_sphere_real
    ⟨x₀, hFG hx₀⟩ hG.1 hG.2
  have hfF : f ∈ supportFunctionals ℝ F :=
    ⟨hfnorm.le, fun x hx => hfG x (hFG hx)⟩
  rw [hF.eq_unitBallSupportFace ℝ hfF]
  intro x hx
  have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hG.2 hx
  exact ⟨mem_closedBall_zero_iff.2 hn.le, hfG x hx⟩

/-- Common support turns a nonempty maximal convex sphere subset into a
maximal proper convex face of the closed ball. -/
theorem isMaximalFace_of_maximal_convex_subset_sphere {F : Set E} (hne : F.Nonempty)
    (hmax : Maximal (fun G : Set E => Convex ℝ G ∧ G ⊆ sphere (0 : E) 1) F) :
    IsMaximalFace F := by
  obtain ⟨f, hfnorm, hfF⟩ := exists_dual_eq_one_of_convex_subset_sphere_real
    hne hmax.1.1 hmax.1.2
  have hsubset : F ⊆ unitBallSupportFace ℝ f := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hmax.1.2 hx
    exact ⟨mem_closedBall_zero_iff.2 hn.le, hfF x hx⟩
  have heq : F = unitBallSupportFace ℝ f := Set.Subset.antisymm hsubset
    (hmax.2 ⟨convex_unitBallSupportFace ℝ f,
      unitBallSupportFace_subset_sphere ℝ hfnorm.le⟩ hsubset)
  refine ⟨hne, hmax.1.1, ?_, ?_, ?_⟩
  · rw [heq]
    exact isExtreme_unitBallSupportFace ℝ hfnorm.le
  · rw [heq]
    exact unitBallSupportFace_ne_closedBall ℝ f
  · intro G hFG hGconv hGext hGne
    exact Set.Subset.antisymm
      (hmax.2 ⟨hGconv, subset_sphere_of_isExtreme_of_ne_closedBall hGext hGne⟩ hFG) hFG

theorem isMaximalFace_iff_maximal_convex_subset_sphere {F : Set E} :
    IsMaximalFace F ↔ F.Nonempty ∧
      Maximal (fun G : Set E => Convex ℝ G ∧ G ⊆ sphere (0 : E) 1) F :=
  ⟨fun hF => ⟨hF.nonempty, hF.maximal_convex_subset_sphere⟩,
    fun h => isMaximalFace_of_maximal_convex_subset_sphere h.1 h.2⟩

/-- Every nonempty convex subset of the sphere is contained in a maximal
proper face. Chain unions supply the bounds required by Zorn's lemma. -/
theorem exists_isMaximalFace_of_convex_subset_sphere {C : Set E}
    (hne : C.Nonempty) (hconv : Convex ℝ C) (hsphere : C ⊆ sphere (0 : E) 1) :
    ∃ F : Set E, C ⊆ F ∧ IsMaximalFace F := by
  let S : Set (Set E) := {G | Convex ℝ G ∧ G ⊆ sphere (0 : E) 1}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc htotal _
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro x hx y hy a b ha hb hab
      obtain ⟨G, hGc, hxG⟩ := hx
      obtain ⟨H, hHc, hyH⟩ := hy
      rcases htotal.total hGc hHc with hGH | hHG
      · exact Set.mem_sUnion_of_mem ((hc hHc).1 (hGH hxG) hyH ha hb hab) hHc
      · exact Set.mem_sUnion_of_mem ((hc hGc).1 hxG (hHG hyH) ha hb hab) hGc
    · rintro x ⟨G, hGc, hxG⟩
      exact (hc hGc).2 hxG
  obtain ⟨F, hCF, hmax⟩ := zorn_subset_nonempty S hchain C ⟨hconv, hsphere⟩
  refine ⟨F, hCF, isMaximalFace_of_maximal_convex_subset_sphere ?_ hmax⟩
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hCF hx⟩

/-- Every unit vector belongs to a maximal face; the zero space has no such
vector, so no nontriviality exception is hidden in this statement. -/
theorem exists_isMaximalFace_of_mem_sphere {x : E} (hx : x ∈ sphere (0 : E) 1) :
    ∃ F : Set E, x ∈ F ∧ IsMaximalFace F := by
  obtain ⟨F, hF, hmax⟩ := exists_isMaximalFace_of_convex_subset_sphere
    (Set.singleton_nonempty x) (convex_singleton x) (Set.singleton_subset_iff.2 hx)
  exact ⟨F, hF (Set.mem_singleton x), hmax⟩

end NormedSpace
