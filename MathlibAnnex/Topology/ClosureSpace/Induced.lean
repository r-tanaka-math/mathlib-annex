/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Maps

/-!
# Induced and subspace closures

The induced closure is `s ↦ f ⁻¹' d.closure (f '' s)`, with no assumption on `f`.
A subspace is the special case of a subtype inclusion. This is not a quotient topology.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ClosureSpace

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Pull back a closure space along any function. -/
def induced (d : ClosureSpace β) (f : α → β) : ClosureSpace α where
  toClosureOperator := ClosureOperator.mk'
    (fun s => f ⁻¹' d.closure (f '' s))
    (by
      intro s t h x hx
      exact d.closure_mono (Set.image_mono h) hx)
    (by
      intro s x hx
      exact d.subset_closure (f '' s) ⟨x, hx, rfl⟩)
    (by
      intro s x hx
      exact d.closure_min (Set.image_preimage_subset f _)
        (d.isClosed_closure (f '' s)) hx)
  map_empty' := by
    change f ⁻¹' d.closure (f '' ∅) = ∅
    rw [Set.image_empty, d.closure_empty, Set.preimage_empty]

@[simp]
theorem induced_closure (d : ClosureSpace β) (f : α → β) (s : Set α) :
    (d.induced f).closure s = f ⁻¹' d.closure (f '' s) := rfl

theorem continuous_induced (d : ClosureSpace β) (f : α → β) :
    (d.induced f).Continuous d f := by
  intro s y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hx

/-- The universal property for a map into an induced closure space. -/
theorem continuous_induced_iff (c : ClosureSpace α) (d : ClosureSpace γ)
    (f : β → γ) (g : α → β) :
    c.Continuous (d.induced f) g ↔ c.Continuous d (f ∘ g) := by
  constructor
  · intro h
    exact (continuous_induced d f).comp h
  · intro h s y hy
    rcases hy with ⟨x, hx, rfl⟩
    change f (g x) ∈ d.closure (f '' (g '' s))
    simpa only [Set.image_image, Function.comp_def] using h s ⟨x, hx, rfl⟩

theorem isTopologizable_induced {d : ClosureSpace β} (hd : d.IsTopologizable)
    (f : α → β) : (d.induced f).IsTopologizable := by
  intro s t
  change f ⁻¹' d.closure (f '' (s ∪ t)) =
    (f ⁻¹' d.closure (f '' s)) ∪ (f ⁻¹' d.closure (f '' t))
  rw [Set.image_union, hd, Set.preimage_union]

theorem image_induced_closure (d : ClosureSpace β) (f : α → β)
    (hf : Function.Surjective f) (s : Set α) :
    f '' (d.induced f).closure s = d.closure (f '' s) := by
  apply Set.Subset.antisymm (continuous_induced d f s)
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, hy, rfl⟩

/-- An equivalence is a homeomorphism from its induced closure space. -/
def homeomorphInduced (d : ClosureSpace β) (e : α ≃ β) :
    Homeomorph (d.induced e) d :=
  Homeomorph.ofImageClosure (d.induced e) d e
    (image_induced_closure d e e.surjective)

/-- The closure on a subset, represented on its subtype. -/
def subspace (c : ClosureSpace α) (A : Set α) : ClosureSpace A :=
  c.induced (Subtype.val : A → α)

@[simp]
theorem subspace_closure (c : ClosureSpace α) (A : Set α) (s : Set A) :
    (c.subspace A).closure s =
      (Subtype.val : A → α) ⁻¹' c.closure ((Subtype.val : A → α) '' s) := rfl

/-- In ambient-set notation the subspace closure is intersection with the subset. -/
theorem image_subspace_closure (c : ClosureSpace α) (A : Set α) (s : Set A) :
    (Subtype.val : A → α) '' (c.subspace A).closure s =
      A ∩ c.closure ((Subtype.val : A → α) '' s) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hxA, hx⟩
    exact ⟨⟨x, hxA⟩, hx, rfl⟩

theorem continuous_subtype_val (c : ClosureSpace α) (A : Set α) :
    (c.subspace A).Continuous c (Subtype.val : A → α) :=
  continuous_induced c Subtype.val

/-- Pullback of a T0 closure is T0 precisely when the inducing map is injective. -/
theorem isT0_induced_iff (d : ClosureSpace β) (hd : d.IsT0) (f : α → β) :
    (d.induced f).IsT0 ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    apply h x y
    · exact d.subset_closure (f '' {y}) ⟨y, Set.mem_singleton y, hxy.symm⟩
    · exact d.subset_closure (f '' {x}) ⟨x, Set.mem_singleton x, hxy⟩
  · intro hf x y hxy hyx
    apply hf
    apply hd (f x) (f y)
    · change f x ∈ d.closure (f '' {y}) at hxy
      simpa only [Set.image_singleton] using hxy
    · change f y ∈ d.closure (f '' {x}) at hyx
      simpa only [Set.image_singleton] using hyx

end ClosureSpace
