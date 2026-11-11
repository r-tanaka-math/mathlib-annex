/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.SquareZero

/-!
# Iterating hereditary splitting along the binary tree

Every node is an actual nonzero positive element of the original algebra.
Both descendants generate smaller hereditary subalgebras, and distinct
nodes at the same depth generate orthogonal hereditary subalgebras.

This is the diagonal hereditary part of a possible matrix construction.
No off-diagonal matrix units, compatibility with the CAR connecting maps,
or surjection onto the CAR completion are asserted here.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

/-- Descendant containment and sibling orthogonality imply orthogonality
of all distinct hereditary corners at a common depth. -/
theorem mul_eq_zero_of_mem_hereditary_binary_tree (f : List Bool → A)
    (hchild : ∀ (s : List Bool) (b : Bool),
      hereditarySubalgebra (f (b :: s)) ≤ hereditarySubalgebra (f s))
    (hsplit : ∀ (s : List Bool) (b c : Bool), b ≠ c →
      ∀ x ∈ hereditarySubalgebra (f (b :: s)),
      ∀ y ∈ hereditarySubalgebra (f (c :: s)), x * y = 0)
    {s t : List Bool} (hlen : s.length = t.length) (hne : s ≠ t)
    {x y : A} (hx : x ∈ hereditarySubalgebra (f s))
    (hy : y ∈ hereditarySubalgebra (f t)) : x * y = 0 := by
  induction s generalizing t x y with
  | nil =>
      have ht : t = [] := by simpa using hlen.symm
      exact (hne ht.symm).elim
  | cons b s ih =>
      cases t with
      | nil => simp at hlen
      | cons c t =>
          have hlen' : s.length = t.length := Nat.succ.inj hlen
          by_cases hst : s = t
          · subst t
            have hbc : b ≠ c := by
              intro h
              exact hne (congrArg (fun z : Bool => z :: s) h)
            exact hsplit s b c hbc x hx y hy
          · exact ih hlen' hst (hchild s b hx) (hchild t c hy)

/-- An antiliminal algebra contains an actual recursively chosen binary
family of nonzero positive hereditary generators below every nonzero positive
generator. All choices stay in the original algebra. -/
theorem IsAntiliminal.exists_hereditary_binary_tree (hA : IsAntiliminal A)
    {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ f : List Bool → A,
      f [] = a ∧
      (∀ s, 0 ≤ f s ∧ f s ≠ 0) ∧
      (∀ (s : List Bool) (b : Bool),
        hereditarySubalgebra (f (b :: s)) ≤ hereditarySubalgebra (f s)) ∧
      (∀ (s : List Bool) (b c : Bool), b ≠ c →
        ∀ x ∈ hereditarySubalgebra (f (b :: s)),
        ∀ y ∈ hereditarySubalgebra (f (c :: s)), x * y = 0) ∧
      (∀ (s t : List Bool), s.length = t.length → s ≠ t →
        ∀ x ∈ hereditarySubalgebra (f s),
        ∀ y ∈ hereditarySubalgebra (f t), x * y = 0) := by
  classical
  let P := {b : A // 0 ≤ b ∧ b ≠ 0}
  have hex (b : P) : ∃ p q : P,
      hereditarySubalgebra p.1 ≤ hereditarySubalgebra b.1 ∧
      hereditarySubalgebra q.1 ≤ hereditarySubalgebra b.1 ∧
      (∀ x ∈ hereditarySubalgebra p.1, ∀ y ∈ hereditarySubalgebra q.1, x * y = 0) ∧
      (∀ y ∈ hereditarySubalgebra q.1, ∀ x ∈ hereditarySubalgebra p.1, y * x = 0) := by
    obtain ⟨p, q, hp, hq, hp0, hq0, hpb, hqb, hpq, hqp⟩ :=
      hA.exists_orthogonal_hereditary_subalgebras b.property.2
    exact ⟨⟨p, hp, hp0⟩, ⟨q, hq, hq0⟩, hpb, hqb, hpq, hqp⟩
  let left (b : P) : P := (hex b).choose
  let right (b : P) : P := (hex b).choose_spec.choose
  have hchoices (b : P) :
      hereditarySubalgebra (left b).1 ≤ hereditarySubalgebra b.1 ∧
      hereditarySubalgebra (right b).1 ≤ hereditarySubalgebra b.1 ∧
      (∀ x ∈ hereditarySubalgebra (left b).1,
        ∀ y ∈ hereditarySubalgebra (right b).1, x * y = 0) ∧
      (∀ y ∈ hereditarySubalgebra (right b).1,
        ∀ x ∈ hereditarySubalgebra (left b).1, y * x = 0) :=
    (hex b).choose_spec.choose_spec
  let node : List Bool → P := fun s =>
    List.rec (⟨a, ha, ha0⟩ : P) (fun b _ z => cond b (right z) (left z)) s
  let f : List Bool → A := fun s => (node s).1
  have hchild (s : List Bool) (b : Bool) :
      hereditarySubalgebra (f (b :: s)) ≤ hereditarySubalgebra (f s) := by
    cases b
    · exact (hchoices (node s)).1
    · exact (hchoices (node s)).2.1
  have hsplit (s : List Bool) (b c : Bool) (hbc : b ≠ c) :
      ∀ x ∈ hereditarySubalgebra (f (b :: s)),
      ∀ y ∈ hereditarySubalgebra (f (c :: s)), x * y = 0 := by
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact (hchoices (node s)).2.2.1
    · exact (hchoices (node s)).2.2.2
    · exact (hbc rfl).elim
  refine ⟨f, rfl, (fun s => (node s).property), hchild, hsplit, ?_⟩
  intro s t hlen hne x hx y hy
  exact mul_eq_zero_of_mem_hereditary_binary_tree f hchild hsplit hlen hne hx hy

end MathlibAnnex.Analysis.CStarAlgebra
