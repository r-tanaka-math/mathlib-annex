/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.SubspaceMaps
public import MathlibAnnex.Topology.ClosureSpace.Components

/-!
# Restrictions to components and to their closures

The two restrictions are separate: a component need not be closed. The comparison
between `Related` and equality requires closedness only of distinct pairs;
closedness of singleton pairs is a further T1 condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ClosureSpace

variable {α : Type u} {β : Type v}

/-- If the generating relation is transitive, its equivalence closure adds no new pairs. -/
theorem related_iff_linked_of_transitive (c : ClosureSpace α)
    (ht : ∀ ⦃a b z : α⦄, c.Linked a b → c.Linked b z → c.Linked a z)
    (x y : α) : c.Related x y ↔ c.Linked x y := by
  constructor
  · intro hxy
    change Relation.EqvGen c.Linked x y at hxy
    induction hxy with
    | rel a b hab => exact hab
    | refl a => exact c.linked_refl a
    | symm a b _ ih => exact c.linked_symm ih
    | trans a b z _ _ ih₁ ih₂ => exact ht ih₁ ih₂
  · exact c.related_of_linked

/-- Distinct-pair closedness is the exact condition for all components to be singletons. -/
theorem forall_related_iff_eq_iff (c : ClosureSpace α) :
    (∀ x y : α, c.Related x y ↔ x = y) ↔
      ∀ x y : α, x ≠ y → c.IsClosed {x, y} := by
  classical
  constructor
  · intro h x y hxy
    by_contra hc
    exact hxy ((h x y).mp (c.related_of_linked (Or.inr hc)))
  · intro h x y
    constructor
    · intro hxy
      change Relation.EqvGen c.Linked x y at hxy
      induction hxy with
      | rel a b hab =>
        rcases hab with hab | hab
        · exact hab
        · by_contra hne
          exact hab (h a b hne)
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro hxy
      subst y
      exact c.related_refl x

/-- With singleton closedness supplied, the preceding exact condition includes all pairs. -/
theorem forall_isClosed_pair_iff (c : ClosureSpace α) :
    (∀ x y : α, c.IsClosed {x, y}) ↔
      c.IsT1 ∧ ∀ x y : α, c.Related x y ↔ x = y := by
  constructor
  · intro h
    refine ⟨fun x => ?_, (c.forall_related_iff_eq_iff).mpr (fun x y _ => h x y)⟩
    simpa using h x x
  · rintro ⟨hT1, h⟩ x y
    by_cases hxy : x = y
    · subst y
      simpa using hT1 x
    · exact (c.forall_related_iff_eq_iff).mp h x y hxy

/-- Restriction to the equivalence class itself, with its existing subspace closure. -/
def Homeomorph.component {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (x : α) :
    Homeomorph (c.subspace (c.component x))
      (d.subspace (d.component (e.toEquiv x))) :=
  e.subspace _ _ (fun y => (e.toFiniteHomeomorph.related_iff x y).symm)

/-- Restriction to the closure of the equivalence class, not to the class itself. -/
def Homeomorph.componentClosure {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (x : α) :
    Homeomorph (c.subspace (c.componentClosure x))
      (d.subspace (d.componentClosure (e.toEquiv x))) := by
  apply e.subspace
  intro y
  rw [← e.image_componentClosure]
  exact ⟨fun hy => ⟨y, hy, rfl⟩,
    fun ⟨z, hz, hzy⟩ => e.toEquiv.injective hzy ▸ hz⟩

@[simp]
theorem Homeomorph.component_apply {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (x : α) (y : c.component x) :
    ((e.component x).toEquiv y).val = e.toEquiv y.val := rfl

@[simp]
theorem Homeomorph.componentClosure_apply {c : ClosureSpace α} {d : ClosureSpace β}
    (e : Homeomorph c d) (x : α) (y : c.componentClosure x) :
    ((e.componentClosure x).toEquiv y).val = e.toEquiv y.val := rfl

end ClosureSpace
