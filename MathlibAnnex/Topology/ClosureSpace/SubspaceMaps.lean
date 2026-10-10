/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Induced

/-!
# Restrictions of maps of closure spaces

All subspaces use `ClosureSpace.subspace`. No finite-union preservation,
separation axiom, or closedness of the subset is required for restrictions.
Ambient closedness is used only when removing the intersection with the subset
from the ambient image of its relative closure.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v}

/-- A continuous map restricts to any two subsets that it maps into one another. -/
theorem Continuous.restrict {c : ClosureSpace α} {d : ClosureSpace β} {f : α → β}
    (hf : c.Continuous d f) {A : Set α} {B : Set β} (hAB : Set.MapsTo f A B) :
    (c.subspace A).Continuous (d.subspace B)
      (fun x : A => (⟨f x.val, hAB x.property⟩ : B)) := by
  intro s y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hfx := hf ((Subtype.val : A → α) '' s) ⟨x.val, hx, rfl⟩
  change f x.val ∈ d.closure ((Subtype.val : B → β) ''
    ((fun z : A => (⟨f z.val, hAB z.property⟩ : B)) '' s))
  simpa only [Set.image_image] using hfx

/-- In particular, restriction to the actual image is continuous. -/
theorem Continuous.restrict_image {c : ClosureSpace α} {d : ClosureSpace β} {f : α → β}
    (hf : c.Continuous d f) (A : Set α) :
    (c.subspace A).Continuous (d.subspace (f '' A))
      (fun x : A => (⟨f x.val, ⟨x.val, x.property, rfl⟩⟩ : f '' A)) :=
  hf.restrict (A := A) (B := f '' A) (fun x hx => ⟨x, hx, rfl⟩)

/-- The inclusion between nested subsets is continuous for the same ambient closure. -/
theorem continuous_inclusion (c : ClosureSpace α) {A B : Set α} (hAB : A ⊆ B) :
    (c.subspace A).Continuous (c.subspace B)
      (fun x : A => (⟨x.val, hAB x.property⟩ : B)) :=
  (continuous_id c).restrict hAB

/-- Relative closed sets are precisely inverse images of ambient closed sets. -/
theorem isClosed_subspace_iff (c : ClosureSpace α) (A : Set α) (s : Set A) :
    (c.subspace A).IsClosed s ↔
      ∃ t : Set α, c.IsClosed t ∧ s = (Subtype.val : A → α) ⁻¹' t := by
  constructor
  · intro hs
    refine ⟨c.closure ((Subtype.val : A → α) '' s), c.isClosed_closure _, ?_⟩
    exact (((c.subspace A).isClosed_iff s).mp hs).symm
  · rintro ⟨t, ht, rfl⟩
    exact (continuous_iff_isClosed_preimage (c.subspace A) c Subtype.val).mp
      (continuous_subtype_val c A) t ht

/-- On an ambient closed subset, the ambient image of the relative closure
is exactly the ambient closure of the image. -/
theorem image_subspace_closure_of_isClosed (c : ClosureSpace α) {A : Set α}
    (hA : c.IsClosed A) (s : Set A) :
    (Subtype.val : A → α) '' (c.subspace A).closure s =
      c.closure ((Subtype.val : A → α) '' s) := by
  rw [image_subspace_closure]
  apply Set.inter_eq_right.mpr
  refine c.closure_min ?_ hA
  rintro x ⟨a, _, rfl⟩
  exact a.property

/-- Closedness in an ambient closed subspace is equivalent to closedness of the image. -/
theorem isClosed_subspace_iff_isClosed_image (c : ClosureSpace α) {A : Set α}
    (hA : c.IsClosed A) (s : Set A) :
    (c.subspace A).IsClosed s ↔ c.IsClosed ((Subtype.val : A → α) '' s) := by
  constructor
  · intro hs
    apply (c.isClosed_iff _).mpr
    rw [← image_subspace_closure_of_isClosed c hA,
      ((c.subspace A).isClosed_iff s).mp hs]
  · intro hs
    apply ((c.subspace A).isClosed_iff_closure_subset s).mpr
    intro x hx
    have hx' : x.val ∈ c.closure ((Subtype.val : A → α) '' s) := hx
    rw [(c.isClosed_iff _).mp hs] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy

namespace Homeomorph

variable {c : ClosureSpace α} {d : ClosureSpace β}

/-- Restrict a closure homeomorphism to subsets corresponding under its actual bijection. -/
def subspace (e : Homeomorph c d) (A : Set α) (B : Set β)
    (hAB : ∀ x : α, x ∈ A ↔ e.toEquiv x ∈ B) :
    Homeomorph (c.subspace A) (d.subspace B) where
  toEquiv :=
    { toFun := fun x => ⟨e.toEquiv x.val, (hAB x.val).mp x.property⟩
      invFun := fun y => ⟨e.toEquiv.symm y.val,
        (hAB (e.toEquiv.symm y.val)).mpr (by
          simpa only [Equiv.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (e.toEquiv.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.toEquiv.apply_symm_apply y.val) }
  continuous_toFun := e.continuous_toFun.restrict (fun x hx => (hAB x).mp hx)
  continuous_invFun := e.continuous_invFun.restrict (fun y hy =>
    (hAB (e.toEquiv.symm y)).mpr (by simpa only [Equiv.apply_symm_apply] using hy))

/-- The restriction of a closure homeomorphism to a subset and its image. -/
def subspaceImage (e : Homeomorph c d) (A : Set α) :
    Homeomorph (c.subspace A) (d.subspace (e.toEquiv '' A)) :=
  e.subspace A (e.toEquiv '' A) (fun x =>
    ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => e.toEquiv.injective hyx ▸ hy⟩)

@[simp]
theorem subspace_apply (e : Homeomorph c d) (A : Set α) (B : Set β)
    (hAB : ∀ x : α, x ∈ A ↔ e.toEquiv x ∈ B) (x : A) :
    ((e.subspace A B hAB).toEquiv x).val = e.toEquiv x.val := rfl

@[simp]
theorem subspace_symm_apply (e : Homeomorph c d) (A : Set α) (B : Set β)
    (hAB : ∀ x : α, x ∈ A ↔ e.toEquiv x ∈ B) (y : B) :
    ((e.subspace A B hAB).toEquiv.symm y).val = e.toEquiv.symm y.val := rfl

@[simp]
theorem subspaceImage_apply (e : Homeomorph c d) (A : Set α) (x : A) :
    ((e.subspaceImage A).toEquiv x).val = e.toEquiv x.val := rfl

@[simp]
theorem subspaceImage_symm_apply (e : Homeomorph c d) (A : Set α)
    (y : e.toEquiv '' A) :
    ((e.subspaceImage A).toEquiv.symm y).val = e.toEquiv.symm y.val := rfl

end Homeomorph

end ClosureSpace
