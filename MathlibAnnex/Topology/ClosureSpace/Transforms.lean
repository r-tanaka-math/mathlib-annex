/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Components
public import MathlibAnnex.Topology.ClosureSpace.Induced

/-!
# The G- and P-transforms

`GPoint` is a quotient by the finite-chain relation. `PPoint` is a subtype of sets:
closures of components. The map `delta` is surjective but need not be injective.
The G-closure is pulled back from P, not obtained from a quotient topology.

The T0 assertion in the opening sentence of Remark 3.26 of the paper needs to
refer to P. The theorem for G below explicitly retains injectivity of `delta`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ClosureSpace

variable {α : Type u}

/-- The set of finite-chain components, represented by an actual quotient. -/
abbrev GPoint (c : ClosureSpace α) : Type u := Quotient c.componentSetoid

/-- The set of closures of components. -/
abbrev PPoint (c : ClosureSpace α) : Type u := {s : Set α // s ∈ Set.range c.componentClosure}

/-- Send a point to its component. -/
def toGPoint (c : ClosureSpace α) (x : α) : c.GPoint := Quotient.mk c.componentSetoid x

/-- Send a point to the closure of its component. -/
def toPPoint (c : ClosureSpace α) (x : α) : c.PPoint :=
  ⟨c.componentClosure x, ⟨x, rfl⟩⟩

theorem toPPoint_eq_of_related (c : ClosureSpace α) {x y : α} (h : c.Related x y) :
    c.toPPoint x = c.toPPoint y := by
  apply Subtype.ext
  exact congrArg c.closure (c.component_eq_of_related h)

theorem nonempty_pPoint (c : ClosureSpace α) (p : c.PPoint) : p.val.Nonempty := by
  obtain ⟨x, hx⟩ := p.property
  rw [← hx]
  exact ⟨x, c.mem_componentClosure x⟩

theorem isClosed_pPoint (c : ClosureSpace α) (p : c.PPoint) : c.IsClosed p.val := by
  obtain ⟨x, hx⟩ := p.property
  rw [← hx]
  exact c.isClosed_closure (c.component x)

/-- Close the component represented by a quotient point. -/
def delta (c : ClosureSpace α) : c.GPoint → c.PPoint :=
  Quotient.lift c.toPPoint (fun _ _ h => c.toPPoint_eq_of_related h)

@[simp]
theorem delta_toGPoint (c : ClosureSpace α) (x : α) :
    c.delta (c.toGPoint x) = c.toPPoint x := rfl

theorem delta_surjective (c : ClosureSpace α) : Function.Surjective c.delta := by
  rintro ⟨p, x, rfl⟩
  exact ⟨c.toGPoint x, rfl⟩

/-- The P-closure formula before packaging its closure axioms. -/
def pClosure (c : ClosureSpace α) (T : Set c.PPoint) : Set c.PPoint :=
  {p | p.val ⊆ c.closure (c.toPPoint ⁻¹' T)}

theorem component_subset_preimage_toPPoint (c : ClosureSpace α) (T : Set c.PPoint)
    {x : α} (hx : c.toPPoint x ∈ T) : c.component x ⊆ c.toPPoint ⁻¹' T := by
  intro y hy
  change c.toPPoint y ∈ T
  rw [← c.toPPoint_eq_of_related hy]
  exact hx

theorem subset_pClosure (c : ClosureSpace α) (T : Set c.PPoint) : T ⊆ c.pClosure T := by
  rintro ⟨p, x, rfl⟩ hp
  exact c.closure_mono (c.component_subset_preimage_toPPoint T hp)

theorem preimage_pClosure_subset_closure (c : ClosureSpace α) (T : Set c.PPoint) :
    c.toPPoint ⁻¹' c.pClosure T ⊆ c.closure (c.toPPoint ⁻¹' T) := by
  intro x hx
  exact hx (c.mem_componentClosure x)

/-- The P-transform as an explicit closure space. -/
def pTransform (c : ClosureSpace α) : ClosureSpace c.PPoint where
  toClosureOperator := ClosureOperator.mk' c.pClosure
    (by
      intro S T h p hp
      exact hp.trans (c.closure_mono (fun _ hx => h hx)))
    c.subset_pClosure
    (by
      intro T p hp x hx
      exact c.closure_min (c.preimage_pClosure_subset_closure T)
        (c.isClosed_closure (c.toPPoint ⁻¹' T)) (hp hx))
  map_empty' := by
    change c.pClosure ∅ = ∅
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨x, hx⟩ := c.nonempty_pPoint p
      have h := hp hx
      simpa only [Set.preimage_empty, c.closure_empty, Set.mem_empty_iff_false] using h
    · exact Set.empty_subset _

@[simp]
theorem pTransform_closure (c : ClosureSpace α) (T : Set c.PPoint) :
    c.pTransform.closure T = c.pClosure T := rfl

/-- The closure of the fiber over a P-point is exactly its underlying set. -/
theorem closure_preimage_toPPoint_singleton (c : ClosureSpace α) (q : c.PPoint) :
    c.closure (c.toPPoint ⁻¹' {q}) = q.val := by
  apply Set.Subset.antisymm
  · apply c.closure_min ?_ (c.isClosed_pPoint q)
    intro x hx
    have hq : c.toPPoint x = q := Set.mem_singleton_iff.1 hx
    have hv : c.componentClosure x = q.val := congrArg Subtype.val hq
    rw [← hv]
    exact c.mem_componentClosure x
  · rcases q with ⟨q, x, rfl⟩
    exact c.closure_mono
      (c.component_subset_preimage_toPPoint {c.toPPoint x} (Set.mem_singleton _))

@[simp]
theorem mem_pTransform_closure_singleton (c : ClosureSpace α) (p q : c.PPoint) :
    p ∈ c.pTransform.closure {q} ↔ p.val ⊆ q.val := by
  change (p.val ⊆ c.closure (c.toPPoint ⁻¹' {q})) ↔ p.val ⊆ q.val
  rw [c.closure_preimage_toPPoint_singleton]

theorem isT0_pTransform (c : ClosureSpace α) : c.pTransform.IsT0 := by
  intro p q hpq hqp
  apply Subtype.ext
  exact Set.Subset.antisymm ((c.mem_pTransform_closure_singleton p q).1 hpq)
    ((c.mem_pTransform_closure_singleton q p).1 hqp)

/-- The G-transform is the pullback of P along the component-closure map. -/
def gTransform (c : ClosureSpace α) : ClosureSpace c.GPoint :=
  c.pTransform.induced c.delta

@[simp]
theorem gTransform_closure (c : ClosureSpace α) (S : Set c.GPoint) :
    c.gTransform.closure S = c.delta ⁻¹' c.pTransform.closure (c.delta '' S) := rfl

theorem continuous_delta (c : ClosureSpace α) :
    c.gTransform.Continuous c.pTransform c.delta := continuous_induced _ _

theorem image_delta_closure (c : ClosureSpace α) (S : Set c.GPoint) :
    c.delta '' c.gTransform.closure S = c.pTransform.closure (c.delta '' S) :=
  image_induced_closure c.pTransform c.delta c.delta_surjective S

/-- The G-transform is T0 exactly when distinct components have distinct closures. -/
theorem isT0_gTransform_iff (c : ClosureSpace α) :
    c.gTransform.IsT0 ↔ Function.Injective c.delta :=
  isT0_induced_iff c.pTransform c.isT0_pTransform c.delta

/-- Under the exact injectivity condition, delta is a homeomorphism. -/
noncomputable def deltaHomeomorph (c : ClosureSpace α) (h : Function.Injective c.delta) :
    Homeomorph c.gTransform c.pTransform :=
  homeomorphInduced c.pTransform (Equiv.ofBijective c.delta ⟨h, c.delta_surjective⟩)

end ClosureSpace
