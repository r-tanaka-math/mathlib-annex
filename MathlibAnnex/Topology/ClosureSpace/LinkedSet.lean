/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Components
public import Mathlib.Order.Minimal

/-!
# Sets of pairwise linked points

These are the R-sets of Definition 6.11. The empty set is permitted. Maximality
is the existing order-theoretic `Maximal` predicate on sets ordered by inclusion,
not a new structure postulating any geometric classification.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v}

/-- Every two points of the set are linked in the ambient closure space. -/
def IsLinkedSet (c : ClosureSpace α) (S : Set α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, c.Linked x y

/-- The empty set is an R-set, with no nonemptiness convention added. -/
theorem isLinkedSet_empty (c : ClosureSpace α) : c.IsLinkedSet ∅ := by
  intro x hx
  exact hx.elim

/-- Reflexivity of `Linked` makes every singleton an R-set. -/
theorem isLinkedSet_singleton (c : ClosureSpace α) (x : α) : c.IsLinkedSet {x} := by
  rintro y rfl z rfl
  exact c.linked_refl _

/-- Taking a subset preserves pairwise linkedness. -/
theorem IsLinkedSet.mono {c : ClosureSpace α} {S T : Set α}
    (hT : c.IsLinkedSet T) (hST : S ⊆ T) : c.IsLinkedSet S :=
  fun x hx y hy => hT x (hST hx) y (hST hy)

/-- The pairwise condition agrees with the existing two-point relation. -/
theorem isLinkedSet_pair_iff (c : ClosureSpace α) (x y : α) :
    c.IsLinkedSet {x, y} ↔ c.Linked x y := by
  constructor
  · intro h
    exact h x (by simp) y (by simp)
  · intro h a ha b hb
    rcases (show a = x ∨ a = y by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha)
      with hax | hay <;>
      rcases (show b = x ∨ b = y by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb)
        with hbx | hby
    · subst a; subst b; exact c.linked_refl x
    · subst a; subst b; exact h
    · subst a; subst b; exact c.linked_symm h
    · subst a; subst b; exact c.linked_refl y

/-- To insert one point, it suffices and is necessary to link it to every old point. -/
theorem isLinkedSet_insert_iff (c : ClosureSpace α) (x : α) (S : Set α) :
    c.IsLinkedSet (insert x S) ↔ c.IsLinkedSet S ∧ ∀ y ∈ S, c.Linked x y := by
  constructor
  · intro h
    exact ⟨h.mono (Set.subset_insert x S), fun y hy => h x (by simp) y (Or.inr hy)⟩
  · rintro ⟨hS, hx⟩ a ha b hb
    rcases Set.mem_insert_iff.mp ha with hax | ha <;>
      rcases Set.mem_insert_iff.mp hb with hbx | hb
    · subst a; subst b; exact c.linked_refl x
    · subst a; exact hx b hb
    · subst b; exact c.linked_symm (hx a ha)
    · exact hS a ha b hb

/-- A nonempty R-set lies in the component of any of its points. -/
theorem IsLinkedSet.subset_component {c : ClosureSpace α} {S : Set α}
    (hS : c.IsLinkedSet S) {x : α} (hx : x ∈ S) : S ⊆ c.component x :=
  fun y hy => c.related_of_linked (hS x hx y hy)

/-- Finite continuity and injectivity are enough for images of R-sets. -/
theorem FinitelyContinuous.isLinkedSet_image {c : ClosureSpace α} {d : ClosureSpace β}
    {f : α → β} (hf : c.FinitelyContinuous d f) (hinj : Function.Injective f)
    {S : Set α} (hS : c.IsLinkedSet S) : d.IsLinkedSet (f '' S) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.linked hinj (hS x hx y hy)

end ClosureSpace
