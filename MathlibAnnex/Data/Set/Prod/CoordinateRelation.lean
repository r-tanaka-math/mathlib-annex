/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.Set.Prod
public import Mathlib.Order.Minimal

/-!
# Sharing a coordinate in a Cartesian product

Rows are `{x} ×ˢ univ`, and columns are `univ ×ˢ {y}`. We use the existing
`Set.Pairwise` and inclusion-order `Maximal`, not a new clique structure.
A nonempty clique lies in a row or column without cardinality hypotheses.
A full row is maximal when the second factor is nontrivial; with an inhabited
second factor this condition can only be dropped when the first is subsingleton.
Empty products and singleton factors are treated separately.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Set

namespace Prod

variable {X : Type u} {Y : Type v}

/-- Two points share at least one coordinate. Equality is permitted. -/
def SharesCoordinate (p q : X × Y) : Prop :=
  p.1 = q.1 ∨ p.2 = q.2

theorem sharesCoordinate_refl (p : X × Y) : SharesCoordinate p p := Or.inl rfl

theorem sharesCoordinate_symm {p q : X × Y} (h : SharesCoordinate p q) :
    SharesCoordinate q p := h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

/-- Swapping the factors preserves the coordinate relation. -/
theorem sharesCoordinate_swap_iff (p q : X × Y) :
    SharesCoordinate p.swap q.swap ↔ SharesCoordinate p q := by
  change (p.2 = q.2 ∨ p.1 = q.1) ↔ (p.1 = q.1 ∨ p.2 = q.2)
  exact or_comm

/-- The diagonal-free `Set.Pairwise` convention agrees with the all-points convention. -/
theorem pairwise_sharesCoordinate_iff (S : Set (X × Y)) :
    S.Pairwise SharesCoordinate ↔ ∀ p ∈ S, ∀ q ∈ S, SharesCoordinate p q := by
  classical
  constructor
  · intro h p hp q hq
    by_cases hpq : p = q
    · subst q
      exact sharesCoordinate_refl p
    · exact h hp hq hpq
  · intro h p hp q hq _
    exact h p hp q hq

/-- Every row is pairwise related, including the empty row. -/
theorem pairwise_sharesCoordinate_singleton_prod (x : X) :
    ({x} ×ˢ (univ : Set Y)).Pairwise SharesCoordinate := by
  intro p hp q hq _
  exact Or.inl ((show p.1 = x from hp.1).trans (show q.1 = x from hq.1).symm)

/-- Every column is pairwise related, including the empty column. -/
theorem pairwise_sharesCoordinate_prod_singleton (y : Y) :
    ((univ : Set X) ×ˢ {y}).Pairwise SharesCoordinate := by
  intro p hp q hq _
  exact Or.inr ((show p.2 = y from hp.2).trans (show q.2 = y from hq.2).symm)

/-- A nonempty set of pairwise related points lies in one full row or column. -/
theorem subset_singleton_prod_or_prod_singleton_of_pairwise
    {S : Set (X × Y)} (hS : S.Pairwise SharesCoordinate) (hne : S.Nonempty) :
    (∃ x : X, S ⊆ {x} ×ˢ univ) ∨ (∃ y : Y, S ⊆ univ ×ˢ {y}) := by
  classical
  obtain ⟨p, hp⟩ := hne
  have hall := (pairwise_sharesCoordinate_iff S).1 hS
  by_cases hfst : ∀ q ∈ S, q.1 = p.1
  · exact Or.inl ⟨p.1, fun q hq => ⟨hfst q hq, mem_univ _⟩⟩
  · simp only [not_forall, _root_.not_imp] at hfst
    obtain ⟨q, hq, hqp⟩ := hfst
    have hqs : q.2 = p.2 := (hall q hq p hp).resolve_left hqp
    refine Or.inr ⟨p.2, ?_⟩
    intro r hr
    refine ⟨mem_univ _, ?_⟩
    change r.2 = p.2
    rcases hall r hr p hp with hrf | hrs
    · rcases hall r hr q hq with hqf | hqr
      · exact (hqp (hqf.symm.trans hrf)).elim
      · exact hqr.trans hqs
    · exact hrs

/-- A maximal clique is nonempty whenever the product is inhabited. -/
theorem nonempty_of_maximal_pairwise_sharesCoordinate [Nonempty (X × Y)]
    {S : Set (X × Y)} (hS : Maximal (fun T => T.Pairwise SharesCoordinate) S) :
    S.Nonempty := by
  classical
  by_contra hn
  have hs : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  subst S
  let p : X × Y := Classical.choice (inferInstance : Nonempty (X × Y))
  have hp : p ∈ (∅ : Set (X × Y)) :=
    hS.2 (pairwise_singleton p SharesCoordinate) (empty_subset _) (show p ∈ ({p} : Set (X × Y)) from rfl)
  exact hp.elim

/-- With two second coordinates, no point outside a full row can be adjoined. -/
theorem maximal_pairwise_sharesCoordinate_singleton_prod [Nontrivial Y] (x : X) :
    Maximal (fun T : Set (X × Y) => T.Pairwise SharesCoordinate) ({x} ×ˢ univ) := by
  classical
  refine ⟨pairwise_sharesCoordinate_singleton_prod x, ?_⟩
  intro T hT hrow p hp
  refine ⟨?_, mem_univ _⟩
  change p.1 = x
  by_contra hpx
  obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  have hall := (pairwise_sharesCoordinate_iff T).1 hT
  have h₁ : p.2 = y₁ :=
    (hall p hp (x, y₁) (hrow ⟨rfl, mem_univ _⟩)).resolve_left hpx
  have h₂ : p.2 = y₂ :=
    (hall p hp (x, y₂) (hrow ⟨rfl, mem_univ _⟩)).resolve_left hpx
  exact hy (h₁.symm.trans h₂)

/-- The corresponding maximality assertion for full columns. -/
theorem maximal_pairwise_sharesCoordinate_prod_singleton [Nontrivial X] (y : Y) :
    Maximal (fun T : Set (X × Y) => T.Pairwise SharesCoordinate) (univ ×ˢ {y}) := by
  classical
  refine ⟨pairwise_sharesCoordinate_prod_singleton y, ?_⟩
  intro T hT hcol p hp
  refine ⟨mem_univ _, ?_⟩
  change p.2 = y
  by_contra hpy
  obtain ⟨x₁, x₂, hx⟩ := exists_pair_ne X
  have hall := (pairwise_sharesCoordinate_iff T).1 hT
  have h₁ : p.1 = x₁ :=
    (hall p hp (x₁, y) (hcol ⟨mem_univ _, rfl⟩)).resolve_right hpy
  have h₂ : p.1 = x₂ :=
    (hall p hp (x₂, y) (hcol ⟨mem_univ _, rfl⟩)).resolve_right hpy
  exact hx (h₁.symm.trans h₂)

/-- For two nontrivial factors the maximal cliques are exactly the rows and columns. -/
theorem maximal_pairwise_sharesCoordinate_iff [Nontrivial X] [Nontrivial Y]
    (S : Set (X × Y)) :
    Maximal (fun T => T.Pairwise SharesCoordinate) S ↔
      (∃ x : X, S = {x} ×ˢ univ) ∨ (∃ y : Y, S = univ ×ˢ {y}) := by
  constructor
  · intro hS
    rcases subset_singleton_prod_or_prod_singleton_of_pairwise hS.1
      (nonempty_of_maximal_pairwise_sharesCoordinate hS) with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, Subset.antisymm hx
        (hS.2 (pairwise_sharesCoordinate_singleton_prod x) hx)⟩
    · exact Or.inr ⟨y, Subset.antisymm hy
        (hS.2 (pairwise_sharesCoordinate_prod_singleton y) hy)⟩
  · rintro (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact maximal_pairwise_sharesCoordinate_singleton_prod x
    · exact maximal_pairwise_sharesCoordinate_prod_singleton y

/-- A subsingleton first factor makes the relation total: only the whole product is maximal. -/
theorem maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_left
    [Subsingleton X] (S : Set (X × Y)) :
    Maximal (fun T => T.Pairwise SharesCoordinate) S ↔ S = univ := by
  have hU : (univ : Set (X × Y)).Pairwise SharesCoordinate :=
    fun _ _ _ _ _ => Or.inl (Subsingleton.elim _ _)
  constructor
  · intro hS
    exact Subset.antisymm (subset_univ _) (hS.2 hU (subset_univ _))
  · rintro rfl
    exact ⟨hU, fun T _ _ => subset_univ T⟩

/-- A subsingleton second factor also makes the relation total. -/
theorem maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_right
    [Subsingleton Y] (S : Set (X × Y)) :
    Maximal (fun T => T.Pairwise SharesCoordinate) S ↔ S = univ := by
  have hU : (univ : Set (X × Y)).Pairwise SharesCoordinate :=
    fun _ _ _ _ _ => Or.inr (Subsingleton.elim _ _)
  constructor
  · intro hS
    exact Subset.antisymm (subset_univ _) (hS.2 hU (subset_univ _))
  · rintro rfl
    exact ⟨hU, fun T _ _ => subset_univ T⟩

/-- If the product is empty, its empty set is the unique maximal clique. -/
theorem maximal_pairwise_sharesCoordinate_iff_eq_empty [IsEmpty (X × Y)]
    (S : Set (X × Y)) :
    Maximal (fun T => T.Pairwise SharesCoordinate) S ↔ S = ∅ := by
  have hs : S = ∅ := Set.ext fun p => isEmptyElim p
  constructor
  · intro _
    exact hs
  · intro _
    refine ⟨?_, ?_⟩
    · intro p
      exact isEmptyElim p
    · intro T _ _ p
      exact isEmptyElim p

/-- Exact row maximality for an inhabited second factor, including singleton factors. -/
theorem maximal_pairwise_sharesCoordinate_singleton_prod_iff [Nonempty Y] (x : X) :
    Maximal (fun T : Set (X × Y) => T.Pairwise SharesCoordinate) ({x} ×ˢ univ) ↔
      Subsingleton X ∨ Nontrivial Y := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial Y with hY | hY
    · letI : Subsingleton Y := hY
      have hrow := (maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_right
        ({x} ×ˢ (univ : Set Y))).1 h
      let y : Y := Classical.choice (inferInstance : Nonempty Y)
      have hfst : ∀ a : X, a = x := by
        intro a
        have hm : (a, y) ∈ ({x} ×ˢ (univ : Set Y)) := hrow.symm ▸ mem_univ _
        exact hm.1
      exact Or.inl ⟨fun a b => (hfst a).trans (hfst b).symm⟩
    · exact Or.inr hY
  · rintro (hX | hY)
    · letI : Subsingleton X := hX
      apply (maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_left _).2
      ext p
      simp only [mem_prod, mem_singleton_iff, mem_univ, and_true, iff_true]
      exact Subsingleton.elim _ _
    · letI : Nontrivial Y := hY
      exact maximal_pairwise_sharesCoordinate_singleton_prod x

/-- Exact column maximality for an inhabited first factor. -/
theorem maximal_pairwise_sharesCoordinate_prod_singleton_iff [Nonempty X] (y : Y) :
    Maximal (fun T : Set (X × Y) => T.Pairwise SharesCoordinate) (univ ×ˢ {y}) ↔
      Nontrivial X ∨ Subsingleton Y := by
  constructor
  · intro h
    rcases subsingleton_or_nontrivial X with hX | hX
    · letI : Subsingleton X := hX
      have hcol := (maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_left
        ((univ : Set X) ×ˢ {y})).1 h
      let x : X := Classical.choice (inferInstance : Nonempty X)
      have hsnd : ∀ b : Y, b = y := by
        intro b
        have hm : (x, b) ∈ ((univ : Set X) ×ˢ {y}) := hcol.symm ▸ mem_univ _
        exact hm.2
      exact Or.inr ⟨fun a b => (hsnd a).trans (hsnd b).symm⟩
    · exact Or.inl hX
  · rintro (hX | hY)
    · letI : Nontrivial X := hX
      exact maximal_pairwise_sharesCoordinate_prod_singleton y
    · letI : Subsingleton Y := hY
      apply (maximal_pairwise_sharesCoordinate_iff_eq_univ_of_subsingleton_right _).2
      ext p
      simp only [mem_prod, mem_singleton_iff, mem_univ, true_and, iff_true]
      exact Subsingleton.elim _ _

/-- A row and a column have exactly their crossing point in common, without size assumptions. -/
theorem singleton_prod_inter_prod_singleton (x : X) (y : Y) :
    ({x} ×ˢ (univ : Set Y)) ∩ (univ ×ˢ {y}) = {(x, y)} := by
  ext p
  constructor
  · intro hp
    exact Prod.ext hp.1.1 hp.2.2
  · intro hp
    change p = (x, y) at hp
    subst p
    exact ⟨⟨rfl, mem_univ _⟩, ⟨mem_univ _, rfl⟩⟩

/-- Distinct rows are disjoint. -/
theorem disjoint_singleton_prod {x x' : X} (h : x ≠ x') :
    Disjoint ({x} ×ˢ (univ : Set Y)) ({x'} ×ˢ univ) := by
  apply Set.disjoint_left.2
  intro p hp hq
  exact h ((show p.1 = x from hp.1).symm.trans hq.1)

/-- Distinct columns are disjoint. -/
theorem disjoint_prod_singleton {y y' : Y} (h : y ≠ y') :
    Disjoint ((univ : Set X) ×ˢ {y}) (univ ×ˢ {y'}) := by
  apply Set.disjoint_left.2
  intro p hp hq
  exact h ((show p.2 = y from hp.2).symm.trans hq.2)

/-- With a nontrivial second factor, a row cannot equal a column. -/
theorem singleton_prod_ne_prod_singleton [Nontrivial Y] (x : X) (y : Y) :
    ({x} ×ˢ (univ : Set Y)) ≠ univ ×ˢ {y} := by
  intro h
  obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  have h₁ : (x, y₁) ∈ ((univ : Set X) ×ˢ {y}) := h ▸ ⟨rfl, mem_univ _⟩
  have h₂ : (x, y₂) ∈ ((univ : Set X) ×ˢ {y}) := h ▸ ⟨rfl, mem_univ _⟩
  exact hy ((show y₁ = y from h₁.2).trans (show y₂ = y from h₂.2).symm)

/-- The coordinate relation is total exactly when at least one factor is subsingleton.
This includes products with an empty factor. -/
theorem pairwise_sharesCoordinate_univ_iff :
    (univ : Set (X × Y)).Pairwise SharesCoordinate ↔ Subsingleton X ∨ Subsingleton Y := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial X with hX | hX
    · exact Or.inl hX
    · letI : Nontrivial X := hX
      rcases subsingleton_or_nontrivial Y with hY | hY
      · exact Or.inr hY
      · letI : Nontrivial Y := hY
        obtain ⟨x₁, x₂, hx⟩ := exists_pair_ne X
        obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
        exact ((pairwise_sharesCoordinate_iff univ).1 h
          (x₁, y₁) (mem_univ _) (x₂, y₂) (mem_univ _)).elim
            (fun hh => (hx hh).elim) (fun hh => (hy hh).elim)
  · rintro (hX | hY)
    · letI : Subsingleton X := hX
      exact fun _ _ _ _ _ => Or.inl (Subsingleton.elim _ _)
    · letI : Subsingleton Y := hY
      exact fun _ _ _ _ _ => Or.inr (Subsingleton.elim _ _)

end Prod
