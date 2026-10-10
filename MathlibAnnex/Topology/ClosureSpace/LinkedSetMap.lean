/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.LinkedSet

/-!
# Finite homeomorphisms transport R-sets and maximal R-sets

All maps are the underlying functions of the existing `FiniteHomeomorph`.
Only finite continuity is used. In particular no statement below assumes or
claims preservation of the closure of an arbitrary infinite set.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v} {c : ClosureSpace α} {d : ClosureSpace β}

/-- The existing finite homeomorphism preserves and reflects individual links. -/
theorem FiniteHomeomorph.linked_iff (e : FiniteHomeomorph c d) (x y : α) :
    d.Linked (e.toEquiv x) (e.toEquiv y) ↔ c.Linked x y := by
  constructor
  · intro h
    have h' := e.finitelyContinuous_invFun.linked e.toEquiv.symm.injective h
    change c.Linked (e.toEquiv.symm (e.toEquiv x)) (e.toEquiv.symm (e.toEquiv y)) at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · exact e.finitelyContinuous_toFun.linked e.toEquiv.injective

/-- Lemma 6.12 with the actual set image under the underlying equivalence. -/
theorem FiniteHomeomorph.isLinkedSet_image_iff (e : FiniteHomeomorph c d) (S : Set α) :
    d.IsLinkedSet (e.toEquiv '' S) ↔ c.IsLinkedSet S := by
  constructor
  · intro h x hx y hy
    exact (e.linked_iff x y).1 (h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  · exact e.finitelyContinuous_toFun.isLinkedSet_image e.toEquiv.injective

/-- The inverse-image version uses finite continuity of the inverse. -/
theorem FiniteHomeomorph.isLinkedSet_preimage_iff (e : FiniteHomeomorph c d) (T : Set β) :
    c.IsLinkedSet (e.toEquiv ⁻¹' T) ↔ d.IsLinkedSet T := by
  constructor
  · intro h y hy z hz
    have h' := (e.linked_iff (e.toEquiv.symm y) (e.toEquiv.symm z)).2
      (h _ (by simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy)
        _ (by simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hz))
    simpa only [Equiv.apply_symm_apply] using h'
  · intro h x hx y hy
    exact (e.linked_iff x y).1 (h _ hx _ hy)

/-- Inclusion-maximal R-sets are sent to inclusion-maximal R-sets. -/
theorem FiniteHomeomorph.maximal_isLinkedSet_image (e : FiniteHomeomorph c d)
    {S : Set α} (hS : Maximal c.IsLinkedSet S) :
    Maximal d.IsLinkedSet (e.toEquiv '' S) := by
  refine ⟨(e.isLinkedSet_image_iff S).2 hS.1, ?_⟩
  intro T hT hST y hy
  have hpre : c.IsLinkedSet (e.toEquiv ⁻¹' T) := (e.isLinkedSet_preimage_iff T).2 hT
  have hSpre : S ⊆ e.toEquiv ⁻¹' T := fun x hx => hST ⟨x, hx, rfl⟩
  have hpreS := hS.2 hpre hSpre
  refine ⟨e.toEquiv.symm y, hpreS ?_, e.toEquiv.apply_symm_apply y⟩
  simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy

/-- Maximality also transports under the actual preimage map. -/
theorem FiniteHomeomorph.maximal_isLinkedSet_preimage (e : FiniteHomeomorph c d)
    {T : Set β} (hT : Maximal d.IsLinkedSet T) :
    Maximal c.IsLinkedSet (e.toEquiv ⁻¹' T) := by
  refine ⟨(e.isLinkedSet_preimage_iff T).2 hT.1, ?_⟩
  intro S hS hTS x hx
  have himage : d.IsLinkedSet (e.toEquiv '' S) := (e.isLinkedSet_image_iff S).2 hS
  have hTimage : T ⊆ e.toEquiv '' S := by
    intro y hy
    refine ⟨e.toEquiv.symm y, hTS ?_, e.toEquiv.apply_symm_apply y⟩
    simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy
  exact hT.2 himage hTimage ⟨x, hx, rfl⟩

/-- Maximality in the source and maximality of the image are equivalent. -/
theorem FiniteHomeomorph.maximal_isLinkedSet_image_iff (e : FiniteHomeomorph c d)
    (S : Set α) :
    Maximal d.IsLinkedSet (e.toEquiv '' S) ↔ Maximal c.IsLinkedSet S := by
  constructor
  · intro h
    have h' := e.maximal_isLinkedSet_preimage h
    have hs : e.toEquiv ⁻¹' (e.toEquiv '' S) = S := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        exact e.toEquiv.injective hyx ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rwa [hs] at h'
  · exact e.maximal_isLinkedSet_image

/-- Maximality of the preimage is equivalent to maximality in the target. -/
theorem FiniteHomeomorph.maximal_isLinkedSet_preimage_iff (e : FiniteHomeomorph c d)
    (T : Set β) :
    Maximal c.IsLinkedSet (e.toEquiv ⁻¹' T) ↔ Maximal d.IsLinkedSet T := by
  constructor
  · intro h
    have h' := e.maximal_isLinkedSet_image h
    have ht : e.toEquiv '' (e.toEquiv ⁻¹' T) = T := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨e.toEquiv.symm y, ?_, e.toEquiv.apply_symm_apply y⟩
        simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy
    rwa [ht] at h'
  · exact e.maximal_isLinkedSet_preimage

end ClosureSpace
