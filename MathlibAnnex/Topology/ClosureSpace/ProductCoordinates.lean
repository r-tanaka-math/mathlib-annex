/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Data.Set.Prod.CoordinateEquiv
public import MathlibAnnex.Topology.ClosureSpace.LinkedSetMap

/-!
# Coordinate presentations of linked sets

A coordinate presentation is an actual equivalence whose `Linked` relation is
identified with `Prod.SharesCoordinate`. We do not package the desired geometric
classification in a structure. The statements are conditional on that point
relation identification, not on any assertion about arbitrary closures.
The operator-algebra-specific construction of a presentation belongs elsewhere.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z a b

open Set

namespace ClosureSpace

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
variable {A : Type a} {B : Type b} {c : ClosureSpace A} {d : ClosureSpace B}

/-- An actual coordinate presentation identifies R-sets with coordinate cliques. -/
theorem isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate (e : X × Y ≃ A)
    (he : ∀ p q, c.Linked (e p) (e q) ↔ Prod.SharesCoordinate p q) (S : Set (X × Y)) :
    c.IsLinkedSet (e '' S) ↔ S.Pairwise Prod.SharesCoordinate := by
  rw [Prod.pairwise_sharesCoordinate_iff]
  constructor
  · intro h p hp q hq
    exact (he p q).1 (h _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩)
  · rintro h _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact (he p q).2 (h p hp q hq)

/-- The same presentation preserves and reflects inclusion-maximality. -/
theorem maximal_isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate (e : X × Y ≃ A)
    (he : ∀ p q, c.Linked (e p) (e q) ↔ Prod.SharesCoordinate p q) (S : Set (X × Y)) :
    Maximal c.IsLinkedSet (e '' S) ↔
      Maximal (fun T => T.Pairwise Prod.SharesCoordinate) S := by
  constructor
  · intro h
    refine ⟨(isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he S).1 h.1, ?_⟩
    intro T hT hST p hp
    have heT := (isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he T).2 hT
    have him : e '' S ⊆ e '' T := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q, hST hq, rfl⟩
    obtain ⟨q, hq, heq⟩ := h.2 heT him ⟨p, hp, rfl⟩
    exact e.injective heq ▸ hq
  · intro h
    refine ⟨(isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he S).2 h.1, ?_⟩
    intro T hT hST p hp
    have hpre : (e ⁻¹' T).Pairwise Prod.SharesCoordinate := by
      intro q hq r hr _
      exact (he q r).1 (hT _ hq _ hr)
    have hSpre : S ⊆ e ⁻¹' T := fun q hq => hST ⟨q, hq, rfl⟩
    refine ⟨e.symm p, h.2 hpre hSpre ?_, e.apply_symm_apply p⟩
    simpa only [mem_preimage, e.apply_symm_apply] using hp

/-- Maximal R-sets in a nondegenerate coordinate presentation are row or column images. -/
theorem maximal_isLinkedSet_iff_eq_image_singleton_prod_or_prod_singleton
    [Nontrivial X] [Nontrivial Y] (e : X × Y ≃ A)
    (he : ∀ p q, c.Linked (e p) (e q) ↔ Prod.SharesCoordinate p q) (T : Set A) :
    Maximal c.IsLinkedSet T ↔
      (∃ x : X, T = e '' ({x} ×ˢ univ)) ∨ (∃ y : Y, T = e '' (univ ×ˢ {y})) := by
  have him : e '' (e ⁻¹' T) = T := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨e.symm p, by simpa only [mem_preimage, e.apply_symm_apply] using hp,
        e.apply_symm_apply p⟩
  constructor
  · intro hT
    have hm := (maximal_isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he
      (e ⁻¹' T)).1 (him.symm ▸ hT)
    rcases (Prod.maximal_pairwise_sharesCoordinate_iff (e ⁻¹' T)).1 hm with
      ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl ⟨x, him.symm.trans (congrArg (fun S => e '' S) hx)⟩
    · exact Or.inr ⟨y, him.symm.trans (congrArg (fun S => e '' S) hy)⟩
  · rintro (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · exact (maximal_isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he _).2
        (Prod.maximal_pairwise_sharesCoordinate_singleton_prod x)
    · exact (maximal_isLinkedSet_image_equiv_iff_pairwise_sharesCoordinate e he _).2
        (Prod.maximal_pairwise_sharesCoordinate_prod_singleton y)

/-- An existing finite homeomorphism has a factor-or-swap formula in actual coordinates.
This gives no converse assertion about continuity from a bare coordinate equivalence. -/
theorem FiniteHomeomorph.exists_prod_equivalences_or_swapped
    [Nonempty X] [Nonempty Y] (h : FiniteHomeomorph c d)
    (s : X × Y ≃ A) (t : X' × Y' ≃ B)
    (hs : ∀ p q, c.Linked (s p) (s q) ↔ Prod.SharesCoordinate p q)
    (ht : ∀ p q, d.Linked (t p) (t q) ↔ Prod.SharesCoordinate p q) :
    (∃ f : X ≃ X', ∃ g : Y ≃ Y',
      ∀ p : X × Y, h.toEquiv (s p) = t (f p.1, g p.2)) ∨
      (∃ f : X ≃ Y', ∃ g : Y ≃ X',
        ∀ p : X × Y, h.toEquiv (s p) = t (g p.2, f p.1)) := by
  let e : X × Y ≃ X' × Y' := (s.trans h.toEquiv).trans t.symm
  have he : ∀ p q, Prod.SharesCoordinate (e p) (e q) ↔ Prod.SharesCoordinate p q := by
    intro p q
    calc
      Prod.SharesCoordinate (e p) (e q) ↔ d.Linked (t (e p)) (t (e q)) := (ht _ _).symm
      _ ↔ d.Linked (h.toEquiv (s p)) (h.toEquiv (s q)) := by
        simp only [e, Equiv.trans_apply, Equiv.apply_symm_apply]
      _ ↔ c.Linked (s p) (s q) := h.linked_iff _ _
      _ ↔ Prod.SharesCoordinate p q := hs p q
  rcases e.exists_prod_equivalences_or_swapped_of_sharesCoordinate_iff_of_nonempty he with
    ⟨f, g, hfg⟩ | ⟨f, g, hfg⟩
  · refine Or.inl ⟨f, g, ?_⟩
    intro p
    simpa only [e, Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg t (hfg p)
  · refine Or.inr ⟨f, g, ?_⟩
    intro p
    simpa only [e, Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg t (hfg p)

end ClosureSpace
