/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Order.Closure
public import Mathlib.Data.Set.Lattice

/-!
# Closure spaces without finite-union preservation

A `ClosureSpace` is explicit data, not a topology or a typeclass. Its order-theoretic
part is Mathlib's `ClosureOperator (Set α)`. Only preservation of the empty set is
added. No finite-union axiom is imposed.

This implements the basic definitions in Section 3 of arXiv:2504.05551v1.
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- An extensive, monotone, idempotent set closure that preserves the empty set. -/
structure ClosureSpace (α : Type u) where
  toClosureOperator : ClosureOperator (Set α)
  map_empty' : toClosureOperator ∅ = ∅

namespace ClosureSpace

variable {α : Type u}

/-- The underlying set closure. -/
def closure (c : ClosureSpace α) : Set α → Set α := c.toClosureOperator

/-- Closedness uses the predicate of the underlying Mathlib closure operator. -/
abbrev IsClosed (c : ClosureSpace α) (s : Set α) : Prop :=
  c.toClosureOperator.IsClosed s

@[simp]
theorem closure_empty (c : ClosureSpace α) : c.closure ∅ = ∅ := c.map_empty'

theorem subset_closure (c : ClosureSpace α) (s : Set α) : s ⊆ c.closure s :=
  c.toClosureOperator.le_closure s

theorem closure_mono (c : ClosureSpace α) {s t : Set α} (h : s ⊆ t) :
    c.closure s ⊆ c.closure t := c.toClosureOperator.monotone h

@[simp]
theorem closure_closure (c : ClosureSpace α) (s : Set α) :
    c.closure (c.closure s) = c.closure s := c.toClosureOperator.idempotent s

@[simp]
theorem closure_univ (c : ClosureSpace α) : c.closure Set.univ = Set.univ :=
  c.toClosureOperator.closure_top

theorem isClosed_iff (c : ClosureSpace α) (s : Set α) :
    c.IsClosed s ↔ c.closure s = s := c.toClosureOperator.isClosed_iff

theorem isClosed_iff_closure_subset (c : ClosureSpace α) (s : Set α) :
    c.IsClosed s ↔ c.closure s ⊆ s := ClosureOperator.isClosed_iff_closure_le

@[simp]
theorem isClosed_closure (c : ClosureSpace α) (s : Set α) : c.IsClosed (c.closure s) :=
  c.toClosureOperator.isClosed_closure s

@[simp]
theorem isClosed_empty (c : ClosureSpace α) : c.IsClosed ∅ :=
  (c.isClosed_iff ∅).2 c.closure_empty

@[simp]
theorem isClosed_univ (c : ClosureSpace α) : c.IsClosed Set.univ :=
  (c.isClosed_iff Set.univ).2 c.closure_univ

theorem closure_min (c : ClosureSpace α) {s t : Set α}
    (hst : s ⊆ t) (ht : c.IsClosed t) : c.closure s ⊆ t :=
  ClosureOperator.closure_min hst ht

theorem isClosed_sInter (c : ClosureSpace α) {S : Set (Set α)}
    (hS : ∀ s ∈ S, c.IsClosed s) : c.IsClosed (⋂₀ S) := by
  apply (c.isClosed_iff_closure_subset _).2
  intro x hx
  apply Set.mem_sInter.2
  intro s hs
  exact c.closure_min (Set.sInter_subset_of_mem hs) (hS s hs) hx

/-- The closure is the intersection of all closed supersets; no topology is used. -/
theorem closure_eq_sInter (c : ClosureSpace α) (s : Set α) :
    c.closure s = ⋂₀ {t : Set α | s ⊆ t ∧ c.IsClosed t} := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_sInter.2
    intro t ht
    exact c.closure_min ht.1 ht.2 hx
  · intro x hx
    exact Set.mem_sInter.1 hx (c.closure s) ⟨c.subset_closure s, c.isClosed_closure s⟩

/-- Finite-union preservation, the extra condition for a topological closure. -/
def IsTopologizable (c : ClosureSpace α) : Prop :=
  ∀ s t : Set α, c.closure (s ∪ t) = c.closure s ∪ c.closure t

theorem isTopologizable_iff (c : ClosureSpace α) :
    c.IsTopologizable ↔ ∀ s t : Set α, c.closure (s ∪ t) ⊆ c.closure s ∪ c.closure t := by
  constructor
  · intro h s t
    exact (h s t).subset
  · intro h s t
    apply Set.Subset.antisymm (h s t)
    intro x hx
    rcases hx with hx | hx
    · exact c.closure_mono Set.subset_union_left hx
    · exact c.closure_mono Set.subset_union_right hx

/-- The specialization preorder of an arbitrary closure space is antisymmetric. -/
def IsT0 (c : ClosureSpace α) : Prop :=
  ∀ x y : α, x ∈ c.closure {y} → y ∈ c.closure {x} → x = y

/-- Every singleton is closed. -/
def IsT1 (c : ClosureSpace α) : Prop := ∀ x : α, c.IsClosed {x}

theorem IsT1.isT0 {c : ClosureSpace α} (h : c.IsT1) : c.IsT0 := by
  intro x y hxy _
  have hy := (c.isClosed_iff {y}).1 (h y)
  rw [hy] at hxy
  exact Set.mem_singleton_iff.1 hxy

end ClosureSpace
