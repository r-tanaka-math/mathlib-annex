/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Topological
public import MathlibAnnex.Topology.ClosureSpace.SubspaceMaps
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Continuity, induced topologies, and homeomorphisms

The maps and their inverses are unchanged when passing between a topologizable
closure space and its ordinary topology. Induction along an arbitrary function
commutes with this passage, so the same statement applies to subspaces without
closedness or nonemptiness assumptions. This file contains no category packaging.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v}

/-- Ordinary continuity for the constructed topologies is exactly closure continuity. -/
theorem continuous_toTopologicalSpace_iff (c : ClosureSpace α) (d : ClosureSpace β)
    (hc : c.IsTopologizable) (hd : d.IsTopologizable) (f : α → β) :
    @_root_.Continuous α β (c.toTopologicalSpace hc) (d.toTopologicalSpace hd) f ↔
      c.Continuous d f := by
  letI : TopologicalSpace α := c.toTopologicalSpace hc
  letI : TopologicalSpace β := d.toTopologicalSpace hd
  rw [_root_.continuous_iff_isClosed,
    ClosureSpace.continuous_iff_isClosed_preimage]
  constructor
  · intro hf s hs
    have hs' := (isClosed_toTopologicalSpace_iff d hd s).mpr hs
    apply (isClosed_toTopologicalSpace_iff c hc (f ⁻¹' s)).mp
    exact hf s hs'
  · intro hf
    intro s hs
    exact (isClosed_toTopologicalSpace_iff c hc (f ⁻¹' s)).mpr
      (hf s ((isClosed_toTopologicalSpace_iff d hd s).mp hs))

/-- The reverse construction preserves continuity in both directions. -/
theorem continuous_ofTopologicalSpace_iff (t : TopologicalSpace α) (r : TopologicalSpace β)
    (f : α → β) : (ofTopologicalSpace t).Continuous (ofTopologicalSpace r) f ↔
      @_root_.Continuous α β t r f := by
  have h := continuous_toTopologicalSpace_iff (ofTopologicalSpace t) (ofTopologicalSpace r)
    (isTopologizable_ofTopologicalSpace t) (isTopologizable_ofTopologicalSpace r) f
  rw [toTopologicalSpace_ofTopologicalSpace, toTopologicalSpace_ofTopologicalSpace] at h
  exact h.symm

/-- Inducing a topology and then taking its closure is the existing induced closure. -/
theorem ofTopologicalSpace_induced (t : TopologicalSpace β) (f : α → β) :
    ofTopologicalSpace (TopologicalSpace.induced f t) = (ofTopologicalSpace t).induced f := by
  apply ClosureSpace.ext
  intro s
  apply Set.ext
  intro x
  change x ∈ @_root_.closure α (TopologicalSpace.induced f t) s ↔
    f x ∈ @_root_.closure β t (f '' s)
  letI : TopologicalSpace β := t
  exact _root_.closure_induced

/-- The topology constructed on an induced closure is the ordinary induced topology. -/
theorem toTopologicalSpace_induced (d : ClosureSpace β) (hd : d.IsTopologizable)
    (f : α → β) :
    (d.induced f).toTopologicalSpace (isTopologizable_induced hd f) =
      TopologicalSpace.induced f (d.toTopologicalSpace hd) := by
  apply toTopologicalSpace_unique
  intro s
  change (ofTopologicalSpace (TopologicalSpace.induced f (d.toTopologicalSpace hd))).closure s =
    (d.induced f).closure s
  rw [ofTopologicalSpace_induced, ofTopologicalSpace_toTopologicalSpace]

/-- In particular the unchanged subspace closure produces the usual subtype topology. -/
theorem toTopologicalSpace_subspace (c : ClosureSpace α) (hc : c.IsTopologizable)
    (A : Set α) :
    (c.subspace A).toTopologicalSpace (isTopologizable_induced hc (Subtype.val : A → α)) =
      TopologicalSpace.induced (Subtype.val : A → α) (c.toTopologicalSpace hc) :=
  toTopologicalSpace_induced c hc (Subtype.val : A → α)

/-- A closure homeomorphism gives an ordinary homeomorphism with the same two functions. -/
def Homeomorph.toTopologicalHomeomorph {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (hc : c.IsTopologizable) (hd : d.IsTopologizable) :
    @_root_.Homeomorph α β (c.toTopologicalSpace hc) (d.toTopologicalSpace hd) := by
  letI : TopologicalSpace α := c.toTopologicalSpace hc
  letI : TopologicalSpace β := d.toTopologicalSpace hd
  exact { toEquiv := e.toEquiv
          continuous_toFun := (continuous_toTopologicalSpace_iff c d hc hd e.toEquiv).mpr
            e.continuous_toFun
          continuous_invFun := (continuous_toTopologicalSpace_iff d c hd hc e.toEquiv.symm).mpr
            e.continuous_invFun }

/-- An ordinary homeomorphism gives a closure homeomorphism for the associated closures. -/
def ofTopologicalHomeomorph {t : TopologicalSpace α} {r : TopologicalSpace β}
    (e : @_root_.Homeomorph α β t r) : Homeomorph (ofTopologicalSpace t) (ofTopologicalSpace r) where
  toEquiv := e.toEquiv
  continuous_toFun := (continuous_ofTopologicalSpace_iff t r e.toEquiv).mpr e.continuous_toFun
  continuous_invFun := (continuous_ofTopologicalSpace_iff r t e.toEquiv.symm).mpr e.continuous_invFun

@[simp]
theorem Homeomorph.toTopologicalHomeomorph_toEquiv {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (hc : c.IsTopologizable) (hd : d.IsTopologizable) :
    @_root_.Homeomorph.toEquiv α β (c.toTopologicalSpace hc) (d.toTopologicalSpace hd)
      (e.toTopologicalHomeomorph hc hd) = e.toEquiv := rfl

@[simp]
theorem ofTopologicalHomeomorph_toEquiv {t : TopologicalSpace α} {r : TopologicalSpace β}
    (e : @_root_.Homeomorph α β t r) : (ofTopologicalHomeomorph e).toEquiv = e.toEquiv := rfl

end ClosureSpace
