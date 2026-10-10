/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Transforms

/-!
# Transport of the G- and P-transforms

A closure-space homeomorphism induces homeomorphisms of both transforms, with
inverses induced by its inverse. The component-closure maps form a commuting square.
This implements Theorem 3.29 of arXiv:2504.05551v1 without a T0 assumption on G.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace
namespace Homeomorph

variable {α : Type u} {β : Type v} {c : ClosureSpace α} {d : ClosureSpace β}

/-- Transport a closed component as an actual image set. -/
def pMap (h : Homeomorph c d) (p : c.PPoint) : d.PPoint :=
  ⟨h.toEquiv '' p.val, by
    obtain ⟨x, hx⟩ := p.property
    refine ⟨h.toEquiv x, ?_⟩
    exact (h.image_componentClosure x).symm.trans
      (congrArg (fun s : Set α => h.toEquiv '' s) hx)⟩

@[simp]
theorem pMap_val (h : Homeomorph c d) (p : c.PPoint) :
    (h.pMap p).val = h.toEquiv '' p.val := rfl

@[simp]
theorem pMap_toPPoint (h : Homeomorph c d) (x : α) :
    h.pMap (c.toPPoint x) = d.toPPoint (h.toEquiv x) := by
  apply Subtype.ext
  exact h.image_componentClosure x

/-- The induced equivalence of P-points; its inverse is induced by the inverse map. -/
def pEquiv (h : Homeomorph c d) : c.PPoint ≃ d.PPoint where
  toFun := h.pMap
  invFun := h.symm.pMap
  left_inv := by
    intro p
    apply Subtype.ext
    change h.toEquiv.symm '' (h.toEquiv '' p.val) = p.val
    simp only [Set.image_image, Equiv.symm_apply_apply]
    exact Set.image_id _
  right_inv := by
    intro p
    apply Subtype.ext
    change h.toEquiv '' (h.toEquiv.symm '' p.val) = p.val
    simp only [Set.image_image, Equiv.apply_symm_apply]
    exact Set.image_id _

theorem continuous_pMap (h : Homeomorph c d) :
    c.pTransform.Continuous d.pTransform h.pMap := by
  intro T q hq
  rcases hq with ⟨p, hp, rfl⟩
  change h.toEquiv '' p.val ⊆ d.closure (d.toPPoint ⁻¹' (h.pMap '' T))
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : x ∈ c.closure (c.toPPoint ⁻¹' T) := hp hx
  have hf := h.continuous_toFun (c.toPPoint ⁻¹' T) ⟨x, hx', rfl⟩
  apply d.closure_mono ?_ hf
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  exact ⟨c.toPPoint a, ha, h.pMap_toPPoint a⟩

/-- The induced homeomorphism of P-transforms. -/
def pHomeomorph (h : Homeomorph c d) : Homeomorph c.pTransform d.pTransform where
  toEquiv := h.pEquiv
  continuous_toFun := h.continuous_pMap
  continuous_invFun := h.symm.continuous_pMap

/-- Transport a component using quotient elimination. -/
def gMap (h : Homeomorph c d) : c.GPoint → d.GPoint :=
  Quotient.lift (fun x => d.toGPoint (h.toEquiv x))
    (fun _ _ hxy => Quotient.sound
      (h.continuous_toFun.finitelyContinuous.related h.toEquiv.injective hxy))

@[simp]
theorem gMap_toGPoint (h : Homeomorph c d) (x : α) :
    h.gMap (c.toGPoint x) = d.toGPoint (h.toEquiv x) := rfl

/-- The induced equivalence of G-points. -/
def gEquiv (h : Homeomorph c d) : c.GPoint ≃ d.GPoint where
  toFun := h.gMap
  invFun := h.symm.gMap
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change c.toGPoint (h.toEquiv.symm (h.toEquiv x)) = c.toGPoint x
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change d.toGPoint (h.toEquiv (h.toEquiv.symm x)) = d.toGPoint x
    rw [Equiv.apply_symm_apply]

/-- Naturality of the component-closure map before bundling continuity. -/
theorem delta_gMap (h : Homeomorph c d) (q : c.GPoint) :
    d.delta (h.gMap q) = h.pMap (c.delta q) := by
  refine Quotient.inductionOn q ?_
  intro x
  exact (h.pMap_toPPoint x).symm

theorem continuous_gMap (h : Homeomorph c d) :
    c.gTransform.Continuous d.gTransform h.gMap := by
  intro S q hq
  rcases hq with ⟨r, hr, rfl⟩
  change d.delta (h.gMap r) ∈ d.pTransform.closure (d.delta '' (h.gMap '' S))
  rw [h.delta_gMap]
  have hr' : c.delta r ∈ c.pTransform.closure (c.delta '' S) := hr
  have hp := h.continuous_pMap (c.delta '' S) ⟨c.delta r, hr', rfl⟩
  have hS : h.pMap '' (c.delta '' S) = d.delta '' (h.gMap '' S) := by
    apply Set.ext
    intro p
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, hp⟩
      exact ⟨h.gMap b, ⟨b, hb, rfl⟩, (h.delta_gMap b).trans hp⟩
    · rintro ⟨a, ⟨b, hb, rfl⟩, hp⟩
      exact ⟨c.delta b, ⟨b, hb, rfl⟩, (h.delta_gMap b).symm.trans hp⟩
  rw [← hS]
  exact hp

/-- The induced homeomorphism of G-transforms. No injectivity of delta is needed. -/
def gHomeomorph (h : Homeomorph c d) : Homeomorph c.gTransform d.gTransform where
  toEquiv := h.gEquiv
  continuous_toFun := h.continuous_gMap
  continuous_invFun := h.symm.continuous_gMap

theorem delta_gHomeomorph (h : Homeomorph c d) (q : c.GPoint) :
    d.delta (h.gHomeomorph.toEquiv q) = h.pHomeomorph.toEquiv (c.delta q) :=
  h.delta_gMap q

end Homeomorph
end ClosureSpace
