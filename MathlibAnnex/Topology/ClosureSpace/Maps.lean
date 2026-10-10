/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Maps of closure spaces

Continuity and finite continuity are distinct predicates. A continuous finite
homeomorphism has no assumption of ordinary continuity for its inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ClosureSpace

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Preservation of closure in the forward direction. -/
def Continuous (c : ClosureSpace α) (d : ClosureSpace β) (f : α → β) : Prop :=
  ∀ s : Set α, f '' c.closure s ⊆ d.closure (f '' s)

/-- Preservation of closure, tested only on finite subsets of the domain. -/
def FinitelyContinuous (c : ClosureSpace α) (d : ClosureSpace β) (f : α → β) : Prop :=
  ∀ s : Set α, s.Finite → f '' c.closure s ⊆ d.closure (f '' s)

theorem continuous_id (c : ClosureSpace α) : c.Continuous c id := by
  intro s x hx
  rcases hx with ⟨y, hy, rfl⟩
  change y ∈ c.closure (id '' s)
  rw [Set.image_id]
  exact hy

theorem Continuous.comp {c : ClosureSpace α} {d : ClosureSpace β} {e : ClosureSpace γ}
    {f : α → β} {g : β → γ} (hg : d.Continuous e g) (hf : c.Continuous d f) :
    c.Continuous e (g ∘ f) := by
  intro s z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hfx : f x ∈ d.closure (f '' s) := hf s ⟨x, hx, rfl⟩
  have hgfx := hg (f '' s) ⟨f x, hfx, rfl⟩
  simpa only [Set.image_image, Function.comp_def] using hgfx

theorem Continuous.finitelyContinuous {c : ClosureSpace α} {d : ClosureSpace β}
    {f : α → β} (hf : c.Continuous d f) : c.FinitelyContinuous d f :=
  fun s _ => hf s

theorem FinitelyContinuous.comp {c : ClosureSpace α} {d : ClosureSpace β}
    {e : ClosureSpace γ} {f : α → β} {g : β → γ}
    (hg : d.FinitelyContinuous e g) (hf : c.FinitelyContinuous d f) :
    c.FinitelyContinuous e (g ∘ f) := by
  intro s hs z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hfx := hf s hs ⟨x, hx, rfl⟩
  have hgfx := hg (f '' s) (hs.image f) ⟨f x, hfx, rfl⟩
  simpa only [Set.image_image, Function.comp_def] using hgfx

/-- Closed-preimage characterization, valid without finite-union preservation. -/
theorem continuous_iff_isClosed_preimage (c : ClosureSpace α) (d : ClosureSpace β)
    (f : α → β) : c.Continuous d f ↔
      ∀ t : Set β, d.IsClosed t → c.IsClosed (f ⁻¹' t) := by
  constructor
  · intro hf t ht
    apply (c.isClosed_iff_closure_subset _).2
    intro x hx
    exact d.closure_min (Set.image_preimage_subset f t) ht
      (hf (f ⁻¹' t) ⟨x, hx, rfl⟩)
  · intro h s y hy
    rcases hy with ⟨x, hx, rfl⟩
    have ht := h (d.closure (f '' s)) (d.isClosed_closure (f '' s))
    apply c.closure_min (t := f ⁻¹' d.closure (f '' s)) ?_ ht hx
    intro a ha
    exact d.subset_closure (f '' s) ⟨a, ha, rfl⟩

/-- A bijection that is continuous in both directions. -/
structure Homeomorph (c : ClosureSpace α) (d : ClosureSpace β) extends α ≃ β where
  continuous_toFun : c.Continuous d toFun
  continuous_invFun : d.Continuous c invFun

namespace Homeomorph

variable {c : ClosureSpace α} {d : ClosureSpace β} {e : ClosureSpace γ}

/-- Reverse a homeomorphism. -/
def symm (h : Homeomorph c d) : Homeomorph d c where
  toEquiv := h.toEquiv.symm
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun

/-- The identity homeomorphism. -/
def refl (c : ClosureSpace α) : Homeomorph c c where
  toEquiv := Equiv.refl α
  continuous_toFun := continuous_id c
  continuous_invFun := continuous_id c

/-- Compose homeomorphisms. -/
def trans (h : Homeomorph c d) (k : Homeomorph d e) : Homeomorph c e where
  toEquiv := h.toEquiv.trans k.toEquiv
  continuous_toFun := k.continuous_toFun.comp h.continuous_toFun
  continuous_invFun := h.continuous_invFun.comp k.continuous_invFun

/-- A homeomorphism transports the full closure exactly. -/
theorem image_closure (h : Homeomorph c d) (s : Set α) :
    h.toEquiv '' c.closure s = d.closure (h.toEquiv '' s) := by
  apply Set.Subset.antisymm (h.continuous_toFun s)
  intro y hy
  have hx := h.continuous_invFun (h.toEquiv '' s) ⟨y, hy, rfl⟩
  change h.toEquiv.symm y ∈ c.closure (h.toEquiv.symm '' (h.toEquiv '' s)) at hx
  have hs : h.toEquiv.symm '' (h.toEquiv '' s) = s := by
    apply Set.ext
    intro x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, ⟨a, ha, rfl⟩, hx⟩
      have hx' : a = x := (h.toEquiv.symm_apply_apply a).symm.trans hx
      exact hx' ▸ ha
    · intro hx
      exact ⟨h.toEquiv x, ⟨x, hx, rfl⟩, h.toEquiv.symm_apply_apply x⟩
  rw [hs] at hx
  exact ⟨h.toEquiv.symm y, hx, h.toEquiv.apply_symm_apply y⟩

/-- A bijection commuting with closure is a homeomorphism. -/
def ofImageClosure (c : ClosureSpace α) (d : ClosureSpace β) (e : α ≃ β)
    (he : ∀ s : Set α, e '' c.closure s = d.closure (e '' s)) : Homeomorph c d where
  toEquiv := e
  continuous_toFun s := (he s).subset
  continuous_invFun := by
    intro t x hx
    rcases hx with ⟨y, hy, rfl⟩
    have ht : e '' (e.symm '' t) = t := by
      apply Set.ext
      intro z
      constructor
      · rintro ⟨a, ⟨b, hb, rfl⟩, hz⟩
        have hz' : b = z := (e.apply_symm_apply b).symm.trans hz
        exact hz' ▸ hb
      · intro hz
        exact ⟨e.symm z, ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩
    have hy' : y ∈ e '' c.closure (e.symm '' t) := by
      rw [he, ht]
      exact hy
    rcases hy' with ⟨a, ha, rfl⟩
    change e.symm (e a) ∈ c.closure (e.symm '' t)
    simpa only [Equiv.symm_apply_apply] using ha

end Homeomorph

/-- A bijection with finite continuity in both directions. -/
structure FiniteHomeomorph (c : ClosureSpace α) (d : ClosureSpace β) extends α ≃ β where
  finitelyContinuous_toFun : c.FinitelyContinuous d toFun
  finitelyContinuous_invFun : d.FinitelyContinuous c invFun

/-- A finite homeomorphism whose forward map is continuous.
Ordinary continuity of the inverse is deliberately not a field. -/
structure ContinuousFiniteHomeomorph (c : ClosureSpace α) (d : ClosureSpace β)
    extends FiniteHomeomorph c d where
  continuous_toFun : c.Continuous d toFun

/-- Forget full continuity and retain finite continuity. -/
def Homeomorph.toFiniteHomeomorph {c : ClosureSpace α} {d : ClosureSpace β}
    (h : Homeomorph c d) : FiniteHomeomorph c d where
  toEquiv := h.toEquiv
  finitelyContinuous_toFun := h.continuous_toFun.finitelyContinuous
  finitelyContinuous_invFun := h.continuous_invFun.finitelyContinuous

/-- Reverse a finite homeomorphism. -/
def FiniteHomeomorph.symm {c : ClosureSpace α} {d : ClosureSpace β}
    (h : FiniteHomeomorph c d) : FiniteHomeomorph d c where
  toEquiv := h.toEquiv.symm
  finitelyContinuous_toFun := h.finitelyContinuous_invFun
  finitelyContinuous_invFun := h.finitelyContinuous_toFun

end ClosureSpace
