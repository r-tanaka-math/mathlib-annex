/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Maps
public import Mathlib.Topology.Closure

/-!
# Topologies associated to topologizable closure spaces

Finite-union preservation, not a separation property, supplies the extra axiom.
The resulting topology has exactly the original closed sets and exactly the original
closure. The reverse construction and both inverse laws are explicit. These are
object-level constructions; no category or functor is postulated here.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v}

/-- Equality of the set closures determines all closure-space data. -/
@[ext]
theorem ext {c d : ClosureSpace α} (h : ∀ s : Set α, c.closure s = d.closure s) :
    c = d := by
  cases c with
  | mk c hc =>
    cases d with
    | mk d hd =>
      have hcd : c = d := ClosureOperator.ext c d h
      cases hcd
      rfl

/-- Finite unions of closed sets are closed under the topologizability hypothesis. -/
theorem IsTopologizable.isClosed_union {c : ClosureSpace α} (hc : c.IsTopologizable)
    {s t : Set α} (hs : c.IsClosed s) (ht : c.IsClosed t) : c.IsClosed (s ∪ t) := by
  apply (c.isClosed_iff _).mpr
  rw [hc s t, (c.isClosed_iff s).mp hs, (c.isClosed_iff t).mp ht]

/-- The ordinary topology whose closed sets are the fixed sets of the original closure. -/
def toTopologicalSpace (c : ClosureSpace α) (hc : c.IsTopologizable) : TopologicalSpace α :=
  TopologicalSpace.ofClosed {s : Set α | c.IsClosed s}
    c.isClosed_empty
    (fun S hS => c.isClosed_sInter (fun s hs => hS hs))
    (fun s hs t ht => hc.isClosed_union hs ht)

@[simp]
theorem isOpen_toTopologicalSpace_iff (c : ClosureSpace α) (hc : c.IsTopologizable)
    (s : Set α) : @_root_.IsOpen α (c.toTopologicalSpace hc) s ↔ c.IsClosed sᶜ :=
  Iff.rfl

/-- The topology construction preserves the entire closed-set family. -/
@[simp]
theorem isClosed_toTopologicalSpace_iff (c : ClosureSpace α) (hc : c.IsTopologizable)
    (s : Set α) : @_root_.IsClosed α (c.toTopologicalSpace hc) s ↔ c.IsClosed s := by
  letI : TopologicalSpace α := c.toTopologicalSpace hc
  constructor
  · intro hs
    have h := hs.isOpen_compl
    change c.IsClosed sᶜᶜ at h
    simpa only [compl_compl] using h
  · intro hs
    refine ⟨?_⟩
    change c.IsClosed sᶜᶜ
    simpa only [compl_compl] using hs

/-- The ordinary closure in the constructed topology is the given closure, on every set. -/
@[simp]
theorem closure_toTopologicalSpace (c : ClosureSpace α) (hc : c.IsTopologizable)
    (s : Set α) : @_root_.closure α (c.toTopologicalSpace hc) s = c.closure s := by
  letI : TopologicalSpace α := c.toTopologicalSpace hc
  apply Set.Subset.antisymm
  · exact _root_.closure_minimal (c.subset_closure s)
      ((isClosed_toTopologicalSpace_iff c hc _).mpr (c.isClosed_closure s))
  · exact c.closure_min _root_.subset_closure
      ((isClosed_toTopologicalSpace_iff c hc _).mp _root_.isClosed_closure)

/-- Every ordinary topology gives the present notion of closure space. -/
def ofTopologicalSpace (t : TopologicalSpace α) : ClosureSpace α := by
  letI : TopologicalSpace α := t
  exact
    { toClosureOperator := ClosureOperator.mk' _root_.closure
        (fun _ _ h => _root_.closure_mono h)
        (fun _ => _root_.subset_closure)
        (fun _ => _root_.closure_closure.subset)
      map_empty' := _root_.closure_empty }

@[simp]
theorem ofTopologicalSpace_closure (t : TopologicalSpace α) (s : Set α) :
    (ofTopologicalSpace t).closure s = @_root_.closure α t s := rfl

/-- A topological closure preserves finite unions. -/
theorem isTopologizable_ofTopologicalSpace (t : TopologicalSpace α) :
    (ofTopologicalSpace t).IsTopologizable := by
  letI : TopologicalSpace α := t
  intro s r
  exact _root_.closure_union

@[simp]
theorem isClosed_ofTopologicalSpace_iff (t : TopologicalSpace α) (s : Set α) :
    (ofTopologicalSpace t).IsClosed s ↔ @_root_.IsClosed α t s := by
  letI : TopologicalSpace α := t
  rw [(ofTopologicalSpace t).isClosed_iff s, ofTopologicalSpace_closure]
  exact _root_.closure_eq_iff_isClosed

/-- Passing from a closure space to its topology and back returns the same data. -/
@[simp]
theorem ofTopologicalSpace_toTopologicalSpace (c : ClosureSpace α)
    (hc : c.IsTopologizable) : ofTopologicalSpace (c.toTopologicalSpace hc) = c := by
  apply ClosureSpace.ext
  intro s
  exact closure_toTopologicalSpace c hc s

/-- Passing from a topology to its closure space and back returns the same topology. -/
@[simp]
theorem toTopologicalSpace_ofTopologicalSpace (t : TopologicalSpace α) :
    (ofTopologicalSpace t).toTopologicalSpace (isTopologizable_ofTopologicalSpace t) = t := by
  apply TopologicalSpace.ext_isClosed
  intro s
  rw [isClosed_toTopologicalSpace_iff, isClosed_ofTopologicalSpace_iff]

/-- A topology with this closure is necessarily the constructed topology. -/
theorem toTopologicalSpace_unique (c : ClosureSpace α) (hc : c.IsTopologizable)
    (t : TopologicalSpace α) (ht : ∀ s, @_root_.closure α t s = c.closure s) :
    c.toTopologicalSpace hc = t := by
  apply TopologicalSpace.ext_isClosed
  intro s
  rw [isClosed_toTopologicalSpace_iff, c.isClosed_iff, ← ht s]
  letI : TopologicalSpace α := t
  exact _root_.closure_eq_iff_isClosed

/-- Finite-union preservation is equivalent to being the closure of an actual topology. -/
theorem isTopologizable_iff_exists_topologicalSpace (c : ClosureSpace α) :
    c.IsTopologizable ↔ ∃ t : TopologicalSpace α,
      ∀ s : Set α, @_root_.closure α t s = c.closure s := by
  constructor
  · intro hc
    exact ⟨c.toTopologicalSpace hc, closure_toTopologicalSpace c hc⟩
  · rintro ⟨t, ht⟩ s r
    letI : TopologicalSpace α := t
    rw [← ht (s ∪ r), ← ht s, ← ht r]
    exact _root_.closure_union

/-- Homeomorphisms preserve topologizability; the proof transports finite unions. -/
theorem Homeomorph.isTopologizable {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (hc : c.IsTopologizable) : d.IsTopologizable := by
  have hi : ∀ S : Set β, e.toEquiv '' (e.toEquiv ⁻¹' S) = S := by
    intro S
    apply Set.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨e.toEquiv.symm y,
        by simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy,
        e.toEquiv.apply_symm_apply y⟩
  intro s t
  calc
    d.closure (s ∪ t) = e.toEquiv '' c.closure (e.toEquiv ⁻¹' (s ∪ t)) := by
      rw [e.image_closure, hi]
    _ = e.toEquiv '' (c.closure (e.toEquiv ⁻¹' s) ∪
        c.closure (e.toEquiv ⁻¹' t)) := by rw [Set.preimage_union, hc]
    _ = d.closure s ∪ d.closure t := by
      rw [Set.image_union, e.image_closure, e.image_closure, hi, hi]

theorem Homeomorph.isTopologizable_iff {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) : c.IsTopologizable ↔ d.IsTopologizable :=
  ⟨e.isTopologizable, e.symm.isTopologizable⟩

end ClosureSpace
