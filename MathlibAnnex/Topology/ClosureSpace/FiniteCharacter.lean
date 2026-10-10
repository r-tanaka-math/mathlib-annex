/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.FiniteHomeomorph

/-!
# Finite character and full continuity

Finite character is stated as an actual equality, without introducing a second
closure operator or a new class. Only the SOURCE needs finite character to
upgrade finite continuity. Both sides are used to upgrade a finite homeomorphism.
There is no assertion that the carrier itself is finite, or that the closure
preserves finite unions.
-/

@[expose] public section
set_option autoImplicit false

universe u v
namespace ClosureSpace
variable {X : Type u} {Y : Type v}

/-- The finite-character closure equation is equivalent to a finite witness
for each point of a closure, including the empty-set case. -/
theorem closure_eq_iUnion_finite_iff (c : ClosureSpace X) :
    (∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t) ↔
    (∀ (s : Set X) (x : X), x ∈ c.closure s →
      ∃ t : Set X, t ⊆ s ∧ t.Finite ∧ x ∈ c.closure t) := by
  constructor
  · intro h s x hx
    rw [h s] at hx
    rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hts, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨ht, hx⟩
    exact ⟨t, hts, ht, hx⟩
  · intro h s
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨t, hts, ht, hxt⟩ := h s x hx
      exact Set.mem_iUnion.mpr ⟨t,
        Set.mem_iUnion.mpr ⟨hts, Set.mem_iUnion.mpr ⟨ht, hxt⟩⟩⟩
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨t, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hts, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨_, hx⟩
      exact c.closure_mono hts hx

/-- A single finite subset giving the whole closure is stronger than finite
character; the subset is allowed to be empty. -/
theorem closure_eq_iUnion_finite_of_exists_finite_subset (c : ClosureSpace X)
    (hc : ∀ s : Set X, ∃ t : Set X,
      t ⊆ s ∧ t.Finite ∧ c.closure t = c.closure s) :
    ∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t := by
  apply (closure_eq_iUnion_finite_iff c).mpr
  intro s x hx
  obtain ⟨t, hts, ht, heq⟩ := hc s
  exact ⟨t, hts, ht, heq.symm ▸ hx⟩

/-- Finite continuity is full continuity when the source has finite character.
No finite character assumption on the target is needed. -/
theorem FinitelyContinuous.continuous_of_closure_eq_iUnion_finite
    {c : ClosureSpace X} {d : ClosureSpace Y} {f : X → Y}
    (hf : c.FinitelyContinuous d f)
    (hc : ∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t) :
    c.Continuous d f := by
  intro s y hy
  rcases hy with ⟨x, hx, rfl⟩
  obtain ⟨t, hts, ht, hxt⟩ := (closure_eq_iUnion_finite_iff c).mp hc s x hx
  exact d.closure_mono (Set.image_mono hts) (hf t ht ⟨x, hxt, rfl⟩)

/-- Upgrade the SAME equivalence using finite character on both sides. -/
def FiniteHomeomorph.toHomeomorphOfFiniteCharacter
    {c : ClosureSpace X} {d : ClosureSpace Y} (e : FiniteHomeomorph c d)
    (hc : ∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t)
    (hd : ∀ s : Set Y, d.closure s =
      ⋃ (t : Set Y) (_ : t ⊆ s) (_ : t.Finite), d.closure t) :
    Homeomorph c d where
  toEquiv := e.toEquiv
  continuous_toFun := e.finitelyContinuous_toFun.continuous_of_closure_eq_iUnion_finite hc
  continuous_invFun := e.finitelyContinuous_invFun.continuous_of_closure_eq_iUnion_finite hd

/-- The upgrade does not reselect its forward or inverse function. -/
@[simp]
theorem FiniteHomeomorph.toHomeomorphOfFiniteCharacter_toEquiv
    {c : ClosureSpace X} {d : ClosureSpace Y} (e : FiniteHomeomorph c d)
    (hc : ∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t)
    (hd : ∀ s : Set Y, d.closure s =
      ⋃ (t : Set Y) (_ : t ⊆ s) (_ : t.Finite), d.closure t) :
    (e.toHomeomorphOfFiniteCharacter hc hd).toEquiv = e.toEquiv := rfl

/-- In particular the original point map preserves every closure, not just
finite closures. -/
theorem FiniteHomeomorph.image_closure_of_closure_eq_iUnion_finite
    {c : ClosureSpace X} {d : ClosureSpace Y} (e : FiniteHomeomorph c d)
    (hc : ∀ s : Set X, c.closure s =
      ⋃ (t : Set X) (_ : t ⊆ s) (_ : t.Finite), c.closure t)
    (hd : ∀ s : Set Y, d.closure s =
      ⋃ (t : Set Y) (_ : t ⊆ s) (_ : t.Finite), d.closure t) (s : Set X) :
    e.toEquiv '' c.closure s = d.closure (e.toEquiv '' s) :=
  (e.toHomeomorphOfFiniteCharacter hc hd).image_closure s

end ClosureSpace
