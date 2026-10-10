/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Transforms
public import Mathlib.Logic.Equiv.Defs

/-!
# Components as sets and as quotient points

The quotient `GPoint` and the family of actual component subsets are different
types. This file gives a bijection, retaining both directions and the exact
component-closure map. No nonemptiness or separation assumption is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace

variable {α : Type u}

/-- Equality of component sets detects the generating equivalence relation. -/
theorem component_eq_iff_related (c : ClosureSpace α) (x y : α) :
    c.component x = c.component y ↔ c.Related x y := by
  constructor
  · intro h
    have hy := c.mem_component y
    rw [← h] at hy
    exact hy
  · exact c.component_eq_of_related

/-- The family of actual component subsets. -/
def componentFamily (c : ClosureSpace α) : Set (Set α) := Set.range c.component

/-- A component represented as a subset, rather than as a quotient element. -/
abbrev ComponentPoint (c : ClosureSpace α) : Type u :=
  {C : Set α // C ∈ c.componentFamily}

/-- The component-set representative associated with an ambient point. -/
def toComponentPoint (c : ClosureSpace α) (x : α) : c.ComponentPoint :=
  ⟨c.component x, ⟨x, rfl⟩⟩

@[simp]
theorem toComponentPoint_eq_iff (c : ClosureSpace α) (x y : α) :
    c.toComponentPoint x = c.toComponentPoint y ↔ c.Related x y := by
  constructor
  · intro h
    exact (c.component_eq_iff_related x y).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (c.component_eq_of_related h)

theorem toComponentPoint_surjective (c : ClosureSpace α) :
    Function.Surjective c.toComponentPoint := by
  rintro ⟨C, x, rfl⟩
  exact ⟨x, rfl⟩

/-- Quotient elimination constructs the map to component subsets. -/
def gPointToComponentPoint (c : ClosureSpace α) : c.GPoint → c.ComponentPoint :=
  Quotient.lift c.toComponentPoint
    (fun x y h => (c.toComponentPoint_eq_iff x y).mpr h)

@[simp]
theorem gPointToComponentPoint_toGPoint (c : ClosureSpace α) (x : α) :
    c.gPointToComponentPoint (c.toGPoint x) = c.toComponentPoint x := rfl

theorem gPointToComponentPoint_bijective (c : ClosureSpace α) :
    Function.Bijective c.gPointToComponentPoint := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y h
    exact Quotient.sound ((c.toComponentPoint_eq_iff x y).mp h)
  · intro C
    obtain ⟨x, rfl⟩ := c.toComponentPoint_surjective C
    exact ⟨c.toGPoint x, rfl⟩

/-- The actual quotient-to-component-set equivalence. -/
noncomputable def gPointEquivComponentPoint (c : ClosureSpace α) :
    c.GPoint ≃ c.ComponentPoint :=
  Equiv.ofBijective c.gPointToComponentPoint c.gPointToComponentPoint_bijective

@[simp]
theorem gPointEquivComponentPoint_toGPoint (c : ClosureSpace α) (x : α) :
    c.gPointEquivComponentPoint (c.toGPoint x) = c.toComponentPoint x := rfl

/-- Closing a component-set representative yields a P-point. -/
def componentPointToPPoint (c : ClosureSpace α) (C : c.ComponentPoint) : c.PPoint :=
  ⟨c.closure C.val, by
    obtain ⟨x, hx⟩ := C.property
    exact ⟨x, congrArg c.closure hx⟩⟩

@[simp]
theorem componentPointToPPoint_toComponentPoint (c : ClosureSpace α) (x : α) :
    c.componentPointToPPoint (c.toComponentPoint x) = c.toPPoint x := rfl

/-- The change of G-point representation commutes with the original delta. -/
theorem componentPointToPPoint_gPointEquivComponentPoint (c : ClosureSpace α)
    (q : c.GPoint) :
    c.componentPointToPPoint (c.gPointEquivComponentPoint q) = c.delta q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

end ClosureSpace
