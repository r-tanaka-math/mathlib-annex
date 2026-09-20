module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# A converse to the Krein--Milman theorem

This file proves the compact-convex form of Milman's converse: an extreme point
of a compact convex set which belongs to the closed convex hull of a subset is
already in the closure of that subset.
-/

@[expose] public section

open Set

variable {E : Type*}

namespace IsCompact

section ConvexJoin

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The convex join of two compact sets in a real topological vector space is compact. -/
theorem convexJoin {s t : Set E} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  let f : ℝ × (E × E) → E := fun p => (1 - p.1) • p.2.1 + p.1 • p.2.2
  have hf : Continuous f :=
    (continuous_const.sub continuous_fst).smul (continuous_fst.comp continuous_snd) |>.add
      (continuous_fst.smul (continuous_snd.comp continuous_snd))
  have hdomain : IsCompact (Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) :=
    isCompact_Icc.prod (hs.prod ht)
  have himage : f '' (Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) = _root_.convexJoin ℝ s t := by
    ext z
    constructor
    · rintro ⟨⟨θ, x, y⟩, ⟨hθ, hx, hy⟩, rfl⟩
      exact mem_convexJoin.2 ⟨x, hx, y, hy, by
        rw [segment_eq_image]
        exact ⟨θ, hθ, rfl⟩⟩
    · rintro hz
      obtain ⟨x, hx, y, hy, hz⟩ := mem_convexJoin.1 hz
      rw [segment_eq_image] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      exact ⟨⟨θ, x, y⟩, ⟨hθ, hx, hy⟩, rfl⟩
  rw [← himage]
  exact hdomain.image hf

end ConvexJoin

end IsCompact

namespace Finset

section FiniteConvexFamily

variable {ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- The convex hull of a finite union of nonempty compact convex sets is compact. -/
theorem isCompact_convexHull_biUnion (t : Finset ι) (D : ι → Set E)
    (hne : ∀ i ∈ t, (D i).Nonempty) (hconv : ∀ i ∈ t, Convex ℝ (D i))
    (hcomp : ∀ i ∈ t, IsCompact (D i)) :
    IsCompact (convexHull ℝ (⋃ i ∈ t, D i)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      by_cases ht : t.Nonempty
      · have htail : (⋃ i ∈ t, D i).Nonempty := by
          obtain ⟨i, hi⟩ := ht
          exact (hne i (mem_insert_of_mem hi)).mono fun z hz =>
            mem_iUnion₂.2 ⟨i, hi, hz⟩
        have ha_nonempty : (D a).Nonempty := hne a (mem_insert_self a t)
        rw [Finset.set_biUnion_insert, convexHull_union ha_nonempty htail]
        rw [Convex.convexHull_eq (hconv a (mem_insert_self a t))]
        exact IsCompact.convexJoin (hcomp a (mem_insert_self a t))
          (ih (fun i hi => hne i (mem_insert_of_mem hi))
            (fun i hi => hconv i (mem_insert_of_mem hi))
            (fun i hi => hcomp i (mem_insert_of_mem hi)))
      · have ht_empty : t = ∅ := not_nonempty_iff_eq_empty.mp ht
        subst t
        simpa [Convex.convexHull_eq (hconv a (mem_insert_self a ∅))] using
          hcomp a (mem_insert_self a ∅)

end FiniteConvexFamily

end Finset

section Milman

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- **Milman's converse.** An extreme point of a compact convex set which lies in the
closed convex hull of a subset lies in the closure of that subset. -/
theorem mem_closure_of_mem_extremePoints_of_mem_closure_convexHull
    {C S : Set E} {x : E} (hCcompact : IsCompact C) (hCconvex : Convex ℝ C)
    (hSC : S ⊆ C) (hxext : x ∈ C.extremePoints ℝ)
    (hx : x ∈ closure (convexHull ℝ S)) : x ∈ closure S := by
  classical
  by_contra hxS
  let K : Set E := closure S
  have hKC : K ⊆ C := closure_minimal hSC hCcompact.isClosed
  have hKcompact : IsCompact K := hCcompact.of_isClosed_subset isClosed_closure hKC
  have hxy (y : K) : x ≠ y.1 := fun h => hxS (h ▸ y.2)
  let f (y : K) : StrongDual ℝ E := Classical.choose (geometric_hahn_banach_point_point (hxy y))
  have hf (y : K) : f y x < f y y.1 :=
    Classical.choose_spec (geometric_hahn_banach_point_point (hxy y))
  let c (y : K) : ℝ := (f y x + f y y.1) / 2
  let U (y : K) : Set E := {z | c y < f y z}
  have hUopen (y : K) : IsOpen (U y) := isOpen_lt continuous_const (f y).continuous
  have hUself (y : K) : y.1 ∈ U y := by
    change (f y x + f y y.1) / 2 < f y y.1
    linarith [hf y]
  have hKcover : K ⊆ ⋃ y : K, U y := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hUself ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover U hUopen hKcover
  let Q (y : K) : Set E := K ∩ {z | c y ≤ f y z}
  let D (y : K) : Set E := closure (convexHull ℝ (Q y))
  have hQnonempty (y : K) : (Q y).Nonempty := by
    refine ⟨y.1, y.2, ?_⟩
    change c y ≤ f y y.1
    exact (show c y < f y y.1 from hUself y).le
  have hDnonempty (y : K) : (D y).Nonempty :=
    (hQnonempty y).mono <| (subset_convexHull ℝ _).trans subset_closure
  have hDconvex (y : K) : Convex ℝ (D y) := (convex_convexHull ℝ _).closure
  have hDC (y : K) : D y ⊆ C :=
    closure_minimal (convexHull_min (fun _ hz => hKC hz.1) hCconvex) hCcompact.isClosed
  have hDcompact (y : K) : IsCompact (D y) :=
    hCcompact.of_isClosed_subset isClosed_closure (hDC y)
  have hDhalf (y : K) : D y ⊆ {z | c y ≤ f y z} := by
    apply closure_minimal
    · exact convexHull_min (fun _ hz => hz.2) (convex_halfSpace_ge (f y).isLinear _)
    · exact isClosed_le continuous_const (f y).continuous
  have hKD : K ⊆ ⋃ y ∈ t, D y := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 (ht hz)
    have hzy' : c y < f y z := hzy
    have hzQ : z ∈ Q y := ⟨hz, hzy'.le⟩
    have hzD : z ∈ D y := subset_closure (subset_convexHull ℝ (Q y) hzQ)
    exact mem_iUnion₂.2 ⟨y, hy, hzD⟩
  let H : Set E := convexHull ℝ (⋃ y ∈ t, D y)
  have hHcompact : IsCompact H :=
    Finset.isCompact_convexHull_biUnion t D
      (fun y hy => hDnonempty y) (fun y hy => hDconvex y) (fun y hy => hDcompact y)
  have hSH : S ⊆ H := fun _ hz =>
    subset_convexHull ℝ _ (hKD (subset_closure hz))
  have hxH : x ∈ H :=
    closure_minimal (convexHull_min hSH (convex_convexHull ℝ _)) hHcompact.isClosed hx
  have hHC : H ⊆ C := convexHull_min (fun _ hz => by
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz
    exact hDC y hzy) hCconvex
  have hxHext : x ∈ H.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset hHC ⟨hxH, hxext⟩
  have hxD : x ∈ ⋃ y ∈ t, D y := extremePoints_convexHull_subset hxHext
  obtain ⟨y, hy, hxyD⟩ := mem_iUnion₂.1 hxD
  have hc : f y x < c y := by
    change f y x < (f y x + f y y.1) / 2
    linarith [hf y]
  exact (not_lt_of_ge (hDhalf y hxyD)) hc

end Milman
