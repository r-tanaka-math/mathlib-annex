/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Data.Set.Prod.CoordinateRelation
public import Mathlib.Logic.Equiv.Prod

/-!
# Equivalences preserving the relation of sharing a coordinate

For inhabited source factors, an equivalence reflecting and preserving this
point relation is a product of two factor equivalences, possibly followed by a
swap. The nontrivial case derives target nontriviality; singleton factors are
handled separately. No factorization is claimed for empty products. Maximal rows
prove uniform orientation, and factor functions are obtained by evaluation at
fixed base points. Their independence of the other coordinate, injectivity,
surjectivity and the inverse formulas are proved explicitly.
No closure, collinearity, field map, or semilinear regularity is asserted here.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open Set Prod

namespace Equiv

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}

/-- Reflection and preservation pass to the actual inverse equivalence. -/
theorem sharesCoordinate_symm_iff (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q)
    (p q : X' × Y') :
    SharesCoordinate (e.symm p) (e.symm q) ↔ SharesCoordinate p q := by
  simpa only [e.apply_symm_apply] using (h (e.symm p) (e.symm q)).symm

/-- Images preserve and reflect the existing `Set.Pairwise` predicate. -/
theorem pairwise_sharesCoordinate_image_iff (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q)
    (S : Set (X × Y)) :
    (e '' S).Pairwise SharesCoordinate ↔ S.Pairwise SharesCoordinate := by
  rw [Prod.pairwise_sharesCoordinate_iff, Prod.pairwise_sharesCoordinate_iff]
  constructor
  · intro hS p hp q hq
    exact (h p q).1 (hS _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩)
  · rintro hS _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact (h p q).2 (hS p hp q hq)

/-- Maximality is transported using the full inverse image of a competing clique. -/
theorem maximal_pairwise_sharesCoordinate_image (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q)
    {S : Set (X × Y)} (hS : Maximal (fun T => T.Pairwise SharesCoordinate) S) :
    Maximal (fun T => T.Pairwise SharesCoordinate) (e '' S) := by
  refine ⟨(e.pairwise_sharesCoordinate_image_iff h S).2 hS.1, ?_⟩
  intro T hT hST b hb
  have hpre : (e ⁻¹' T).Pairwise SharesCoordinate := by
    intro p hp q hq _
    exact (h p q).1 ((Prod.pairwise_sharesCoordinate_iff T).1 hT _ hp _ hq)
  have hSpre : S ⊆ e ⁻¹' T := fun p hp => hST ⟨p, hp, rfl⟩
  refine ⟨e.symm b, hS.2 hpre hSpre ?_, e.apply_symm_apply b⟩
  simpa only [mem_preimage, e.apply_symm_apply] using hb

/-- Distinct coordinates in the source force both target factors to be nontrivial. -/
theorem nontrivial_factors_of_sharesCoordinate_iff [Nontrivial X] [Nontrivial Y]
    (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) :
    Nontrivial X' ∧ Nontrivial Y' := by
  obtain ⟨x₁, x₂, hx⟩ := exists_pair_ne X
  obtain ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  have hn : ¬ SharesCoordinate (e (x₁, y₁)) (e (x₂, y₂)) := by
    intro hh
    exact ((h _ _).1 hh).elim hx hy
  exact ⟨⟨⟨(e (x₁, y₁)).1, (e (x₂, y₂)).1, fun hh => hn (Or.inl hh)⟩⟩,
    ⟨⟨(e (x₁, y₁)).2, (e (x₂, y₂)).2, fun hh => hn (Or.inr hh)⟩⟩⟩

/-- An image row is a full row or full column, not merely a subset of one. -/
theorem image_singleton_prod_eq_or_eq_prod_singleton
    [Nontrivial Y] [Nontrivial X'] [Nontrivial Y']
    (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) (x : X) :
    (∃ a : X', e '' ({x} ×ˢ univ) = {a} ×ˢ univ) ∨
      (∃ b : Y', e '' ({x} ×ˢ univ) = univ ×ˢ {b}) :=
  (Prod.maximal_pairwise_sharesCoordinate_iff _).1
    (e.maximal_pairwise_sharesCoordinate_image h
      (Prod.maximal_pairwise_sharesCoordinate_singleton_prod x))

/-- Once one row maps to a row, every row does. Distinct rows cannot meet a column image. -/
theorem forall_image_singleton_prod_eq_singleton_prod
    [Nontrivial Y] [Nontrivial X'] [Nontrivial Y']
    (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q)
    (x₀ : X) (a₀ : X') (h₀ : e '' ({x₀} ×ˢ univ) = {a₀} ×ˢ univ) :
    ∀ x : X, ∃ a : X', e '' ({x} ×ˢ univ) = {a} ×ˢ univ := by
  intro x
  rcases e.image_singleton_prod_eq_or_eq_prod_singleton h x with hr | ⟨b, hc⟩
  · exact hr
  · have hm₀ : (a₀, b) ∈ e '' ({x₀} ×ˢ univ) := h₀.symm ▸ ⟨rfl, mem_univ _⟩
    have hmx : (a₀, b) ∈ e '' ({x} ×ˢ univ) := hc.symm ▸ ⟨mem_univ _, rfl⟩
    obtain ⟨p, hp, hep⟩ := hm₀
    obtain ⟨q, hq, heq⟩ := hmx
    have hpq : p = q := e.injective (hep.trans heq.symm)
    have hxx : x = x₀ :=
      (show q.1 = x from hq.1).symm.trans
        ((congrArg Prod.fst hpq).symm.trans (show p.1 = x₀ from hp.1))
    subst x
    exact (Prod.singleton_prod_ne_prod_singleton a₀ b (h₀.symm.trans hc)).elim

/-- Uniform row orientation constructs two actual factor equivalences.
The base points used to define the functions disappear from their evaluation law. -/
theorem exists_prod_equivalences_of_image_singleton_prod
    [Nonempty X] [Nonempty Y] (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q)
    (hrow : ∀ x : X, ∃ a : X', e '' ({x} ×ˢ univ) = {a} ×ˢ univ) :
    ∃ f : X ≃ X', ∃ g : Y ≃ Y', ∀ p : X × Y, e p = (f p.1, g p.2) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let y₀ : Y := Classical.choice (inferInstance : Nonempty Y)
  let f : X → X' := fun x => (e (x, y₀)).1
  have hr : ∀ x : X, e '' ({x} ×ˢ univ) = {f x} ×ˢ univ := by
    intro x
    obtain ⟨a, ha⟩ := hrow x
    have hm : e (x, y₀) ∈ ({a} ×ˢ (univ : Set Y')) :=
      ha ▸ (show e (x, y₀) ∈ e '' ({x} ×ˢ univ) from
        ⟨(x, y₀), ⟨rfl, mem_univ _⟩, rfl⟩)
    have hfa : f x = a := hm.1
    simpa only [hfa] using ha
  have hfval : ∀ x y, (e (x, y)).1 = f x := by
    intro x y
    have hm : e (x, y) ∈ ({f x} ×ˢ (univ : Set Y')) :=
      hr x ▸ (show e (x, y) ∈ e '' ({x} ×ˢ univ) from
        ⟨(x, y), ⟨rfl, mem_univ _⟩, rfl⟩)
    exact hm.1
  have hfi : Function.Injective f := by
    intro x₁ x₂ hfx
    have hm : e (x₁, y₀) ∈ e '' ({x₂} ×ˢ univ) :=
      (hr x₂).symm ▸ (show e (x₁, y₀) ∈ ({f x₂} ×ˢ (univ : Set Y')) from
        ⟨hfx, mem_univ _⟩)
    obtain ⟨p, hp, heq⟩ := hm
    exact (congrArg Prod.fst (e.injective heq)).symm.trans hp.1
  let g : Y → Y' := fun y => (e (x₀, y)).2
  have hgval : ∀ x y, (e (x, y)).2 = g y := by
    intro x y
    by_cases hx : x = x₀
    · subst x
      rfl
    · rcases (h (x, y) (x₀, y)).2 (Or.inr rfl) with hfst | hsnd
      · exact (hx (hfi ((hfval x y).symm.trans (hfst.trans (hfval x₀ y))))).elim
      · exact hsnd
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨⟨x, y⟩, heq⟩ := e.surjective (a, g y₀)
    exact ⟨x, (hfval x y).symm.trans (congrArg Prod.fst heq)⟩
  have hgi : Function.Injective g := by
    intro y₁ y₂ hgy
    have heq : e (x₀, y₁) = e (x₀, y₂) :=
      Prod.ext ((hfval x₀ y₁).trans (hfval x₀ y₂).symm) hgy
    exact congrArg Prod.snd (e.injective heq)
  have hgs : Function.Surjective g := by
    intro b
    obtain ⟨⟨x, y⟩, heq⟩ := e.surjective (f x₀, b)
    exact ⟨y, (hgval x y).symm.trans (congrArg Prod.snd heq)⟩
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, Equiv.ofBijective g ⟨hgi, hgs⟩, ?_⟩
  rintro ⟨x, y⟩
  exact Prod.ext (hfval x y) (hgval x y)

/-- Every coordinate-relation equivalence of nontrivial products has a uniform orientation. -/
theorem exists_prod_equivalences_or_swapped_of_sharesCoordinate_iff
    [Nontrivial X] [Nontrivial Y] (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) :
    (∃ f : X ≃ X', ∃ g : Y ≃ Y', ∀ p : X × Y, e p = (f p.1, g p.2)) ∨
      (∃ f : X ≃ Y', ∃ g : Y ≃ X', ∀ p : X × Y, e p = (g p.2, f p.1)) := by
  classical
  obtain ⟨hX', hY'⟩ := e.nontrivial_factors_of_sharesCoordinate_iff h
  letI : Nontrivial X' := hX'
  letI : Nontrivial Y' := hY'
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  rcases e.image_singleton_prod_eq_or_eq_prod_singleton h x₀ with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Or.inl (e.exists_prod_equivalences_of_image_singleton_prod h
      (e.forall_image_singleton_prod_eq_singleton_prod h x₀ a ha))
  · let e' : X × Y ≃ Y' × X' := e.trans (Equiv.prodComm X' Y')
    have h' : ∀ p q, SharesCoordinate (e' p) (e' q) ↔ SharesCoordinate p q := by
      intro p q
      exact (Prod.sharesCoordinate_swap_iff (e p) (e q)).trans (h p q)
    have hb' : e' '' ({x₀} ×ˢ univ) = {b} ×ˢ univ := by
      ext t
      constructor
      · rintro ⟨p, hp, hpt⟩
        have hm : e p ∈ ((univ : Set X') ×ˢ {b}) := hb ▸ ⟨p, hp, rfl⟩
        refine ⟨?_, mem_univ _⟩
        change t.1 = b
        exact (congrArg Prod.fst hpt).symm.trans hm.2
      · intro ht
        have hm : t.swap ∈ e '' ({x₀} ×ˢ univ) := hb.symm ▸ ⟨mem_univ _, ht.1⟩
        obtain ⟨p, hp, hpt⟩ := hm
        refine ⟨p, hp, ?_⟩
        change (e p).swap = t
        simpa only [Prod.swap_swap] using congrArg Prod.swap hpt
    obtain ⟨f, g, hfg⟩ := e'.exists_prod_equivalences_of_image_singleton_prod h'
      (e'.forall_image_singleton_prod_eq_singleton_prod h' x₀ b hb')
    refine Or.inr ⟨f, g, ?_⟩
    intro p
    exact Prod.ext (congrArg Prod.snd (hfg p)) (congrArg Prod.fst (hfg p))

/-- Two inhabited products with subsingleton first factors have the unswapped decomposition.
No nontriviality or choice of a unique maximal-row orientation is required. -/
theorem exists_prod_equivalences_of_subsingleton_first_factors
    [Nonempty X] [Nonempty Y] [Subsingleton X] [Subsingleton X']
    (e : X × Y ≃ X' × Y') :
    ∃ f : X ≃ X', ∃ g : Y ≃ Y', ∀ p : X × Y, e p = (f p.1, g p.2) := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let y₀ : Y := Classical.choice (inferInstance : Nonempty Y)
  have h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q := by
    intro p q
    exact ⟨fun _ => Or.inl (Subsingleton.elim _ _),
      fun _ => Or.inl (Subsingleton.elim _ _)⟩
  apply e.exists_prod_equivalences_of_image_singleton_prod h
  intro x
  refine ⟨(e (x₀, y₀)).1, ?_⟩
  ext p
  constructor
  · intro _
    exact ⟨Subsingleton.elim _ _, mem_univ _⟩
  · intro _
    obtain ⟨q, rfl⟩ := e.surjective p
    exact ⟨q, ⟨Subsingleton.elim _ _, mem_univ _⟩, rfl⟩

/-- With a singleton first source factor, totality detects the singleton target factor. -/
theorem exists_prod_equivalences_or_swapped_of_subsingleton_left
    [Nonempty X] [Nonempty Y] [Subsingleton X] (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) :
    (∃ f : X ≃ X', ∃ g : Y ≃ Y', ∀ p : X × Y, e p = (f p.1, g p.2)) ∨
      (∃ f : X ≃ Y', ∃ g : Y ≃ X', ∀ p : X × Y, e p = (g p.2, f p.1)) := by
  have ht : (univ : Set (X' × Y')).Pairwise SharesCoordinate := by
    intro p _ q _ _
    have hh := (h (e.symm p) (e.symm q)).2 (Or.inl (Subsingleton.elim _ _))
    simpa only [e.apply_symm_apply] using hh
  rcases Prod.pairwise_sharesCoordinate_univ_iff.1 ht with hX' | hY'
  · letI : Subsingleton X' := hX'
    exact Or.inl (e.exists_prod_equivalences_of_subsingleton_first_factors)
  · letI : Subsingleton Y' := hY'
    let e' : X × Y ≃ Y' × X' := e.trans (Equiv.prodComm X' Y')
    obtain ⟨f, g, hfg⟩ := e'.exists_prod_equivalences_of_subsingleton_first_factors
    refine Or.inr ⟨f, g, ?_⟩
    intro p
    exact Prod.ext (congrArg Prod.snd (hfg p)) (congrArg Prod.fst (hfg p))

/-- The factor-or-swap decomposition holds for all inhabited source products.
Nontrivial factors are needed for unique orientation, not for this disjunction. -/
theorem exists_prod_equivalences_or_swapped_of_sharesCoordinate_iff_of_nonempty
    [Nonempty X] [Nonempty Y] (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) :
    (∃ f : X ≃ X', ∃ g : Y ≃ Y', ∀ p : X × Y, e p = (f p.1, g p.2)) ∨
      (∃ f : X ≃ Y', ∃ g : Y ≃ X', ∀ p : X × Y, e p = (g p.2, f p.1)) := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · letI : Subsingleton X := hX
    exact e.exists_prod_equivalences_or_swapped_of_subsingleton_left h
  · letI : Nontrivial X := hX
    rcases subsingleton_or_nontrivial Y with hY | hY
    · letI : Subsingleton Y := hY
      let e' : Y × X ≃ X' × Y' := (Equiv.prodComm Y X).trans e
      have h' : ∀ p q, SharesCoordinate (e' p) (e' q) ↔ SharesCoordinate p q := by
        intro p q
        exact (h p.swap q.swap).trans (Prod.sharesCoordinate_swap_iff p q)
      rcases e'.exists_prod_equivalences_or_swapped_of_subsingleton_left h' with
        ⟨f, g, hfg⟩ | ⟨f, g, hfg⟩
      · refine Or.inr ⟨g, f, ?_⟩
        intro p
        exact hfg p.swap
      · refine Or.inl ⟨g, f, ?_⟩
        intro p
        exact hfg p.swap
    · letI : Nontrivial Y := hY
      exact e.exists_prod_equivalences_or_swapped_of_sharesCoordinate_iff h

/-- The decomposition also holds as an equality of the actual bundled equivalences. -/
theorem exists_prodCongr_or_prodCongr_trans_prodComm_of_sharesCoordinate_iff
    [Nonempty X] [Nonempty Y] (e : X × Y ≃ X' × Y')
    (h : ∀ p q, SharesCoordinate (e p) (e q) ↔ SharesCoordinate p q) :
    (∃ f : X ≃ X', ∃ g : Y ≃ Y', e = Equiv.prodCongr f g) ∨
      (∃ f : X ≃ Y', ∃ g : Y ≃ X',
        e = (Equiv.prodCongr f g).trans (Equiv.prodComm Y' X')) := by
  rcases e.exists_prod_equivalences_or_swapped_of_sharesCoordinate_iff_of_nonempty h with
    ⟨f, g, hfg⟩ | ⟨f, g, hfg⟩
  · exact Or.inl ⟨f, g, Equiv.ext hfg⟩
  · exact Or.inr ⟨f, g, Equiv.ext hfg⟩

/-- The inverse in the unswapped orientation has the coordinatewise inverse formula. -/
theorem symm_apply_of_apply_eq_prod (e : X × Y ≃ X' × Y') (f : X ≃ X') (g : Y ≃ Y')
    (h : ∀ p : X × Y, e p = (f p.1, g p.2)) (p : X' × Y') :
    e.symm p = (f.symm p.1, g.symm p.2) := by
  apply e.injective
  rw [e.apply_symm_apply, h]
  simp only [f.apply_symm_apply, g.apply_symm_apply]

/-- The inverse in the swapped orientation exchanges the target coordinates first. -/
theorem symm_apply_of_apply_eq_swapped_prod (e : X × Y ≃ X' × Y')
    (f : X ≃ Y') (g : Y ≃ X')
    (h : ∀ p : X × Y, e p = (g p.2, f p.1)) (p : X' × Y') :
    e.symm p = (f.symm p.2, g.symm p.1) := by
  apply e.injective
  rw [e.apply_symm_apply, h]
  simp only [f.apply_symm_apply, g.apply_symm_apply]

/-- In the unswapped orientation, all row images are the corresponding full rows. -/
theorem image_singleton_prod_of_apply_eq_prod (e : X × Y ≃ X' × Y')
    (f : X ≃ X') (g : Y ≃ Y')
    (h : ∀ p : X × Y, e p = (f p.1, g p.2)) (x : X) :
    e '' ({x} ×ˢ univ) = {f x} ×ˢ univ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [h]
    exact ⟨congrArg f hq.1, mem_univ _⟩
  · intro hp
    refine ⟨(x, g.symm p.2), ⟨rfl, mem_univ _⟩, ?_⟩
    rw [h]
    exact Prod.ext (show p.1 = f x from hp.1).symm (g.apply_symm_apply p.2)

/-- In the unswapped orientation, all column images are the corresponding full columns. -/
theorem image_prod_singleton_of_apply_eq_prod (e : X × Y ≃ X' × Y')
    (f : X ≃ X') (g : Y ≃ Y')
    (h : ∀ p : X × Y, e p = (f p.1, g p.2)) (y : Y) :
    e '' (univ ×ˢ {y}) = univ ×ˢ {g y} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [h]
    exact ⟨mem_univ _, congrArg g hq.2⟩
  · intro hp
    refine ⟨(f.symm p.1, y), ⟨mem_univ _, rfl⟩, ?_⟩
    rw [h]
    exact Prod.ext (f.apply_symm_apply p.1) (show p.2 = g y from hp.2).symm

/-- Products of factor equivalences preserve and reflect the point relation. -/
theorem sharesCoordinate_prodCongr_iff (f : X ≃ X') (g : Y ≃ Y') (p q : X × Y) :
    SharesCoordinate (Equiv.prodCongr f g p) (Equiv.prodCongr f g q) ↔
      SharesCoordinate p q := by
  change (f p.1 = f q.1 ∨ g p.2 = g q.2) ↔ (p.1 = q.1 ∨ p.2 = q.2)
  exact or_congr f.injective.eq_iff g.injective.eq_iff

/-- The swapped products also preserve and reflect the point relation. -/
theorem sharesCoordinate_prodCongr_trans_prodComm_iff
    (f : X ≃ Y') (g : Y ≃ X') (p q : X × Y) :
    SharesCoordinate ((Equiv.prodCongr f g).trans (Equiv.prodComm Y' X') p)
      ((Equiv.prodCongr f g).trans (Equiv.prodComm Y' X') q) ↔
      SharesCoordinate p q :=
  (Prod.sharesCoordinate_swap_iff _ _).trans (sharesCoordinate_prodCongr_iff f g p q)

/-- In the swapped orientation, all rows map to full columns. -/
theorem image_singleton_prod_of_apply_eq_swapped_prod (e : X × Y ≃ X' × Y')
    (f : X ≃ Y') (g : Y ≃ X')
    (h : ∀ p : X × Y, e p = (g p.2, f p.1)) (x : X) :
    e '' ({x} ×ˢ univ) = univ ×ˢ {f x} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [h]
    exact ⟨mem_univ _, congrArg f hq.1⟩
  · intro hp
    refine ⟨(x, g.symm p.1), ⟨rfl, mem_univ _⟩, ?_⟩
    rw [h]
    exact Prod.ext (g.apply_symm_apply p.1) (show p.2 = f x from hp.2).symm

/-- In the swapped orientation, all columns map to full rows. -/
theorem image_prod_singleton_of_apply_eq_swapped_prod (e : X × Y ≃ X' × Y')
    (f : X ≃ Y') (g : Y ≃ X')
    (h : ∀ p : X × Y, e p = (g p.2, f p.1)) (y : Y) :
    e '' (univ ×ˢ {y}) = {g y} ×ˢ univ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [h]
    exact ⟨congrArg g hq.2, mem_univ _⟩
  · intro hp
    refine ⟨(f.symm p.2, y), ⟨mem_univ _, rfl⟩, ?_⟩
    rw [h]
    exact Prod.ext (show p.1 = g y from hp.1).symm (f.apply_symm_apply p.2)

/-- Nontrivial factors prevent the two global orientations from holding simultaneously. -/
theorem not_apply_eq_prod_and_swapped_prod [Nontrivial X] [Nonempty Y]
    (e : X × Y ≃ X' × Y') (f : X ≃ X') (g : Y ≃ Y')
    (f' : X ≃ Y') (g' : Y ≃ X') :
    ¬ ((∀ p : X × Y, e p = (f p.1, g p.2)) ∧
      (∀ p : X × Y, e p = (g' p.2, f' p.1))) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨x₁, x₂, hx⟩ := exists_pair_ne X
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  have hy₁ : g y = f' x₁ := congrArg Prod.snd ((h₁ (x₁, y)).symm.trans (h₂ (x₁, y)))
  have hy₂ : g y = f' x₂ := congrArg Prod.snd ((h₁ (x₂, y)).symm.trans (h₂ (x₂, y)))
  exact hx (f'.injective (hy₁.symm.trans hy₂))

end Equiv
