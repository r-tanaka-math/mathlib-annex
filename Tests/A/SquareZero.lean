/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.SquareZero

/-! Typed consumers start from noncommutativity or antiliminality, and derive
the nonzero square-zero witness. No nilpotent or splitting conclusion is
inserted into a consumer hypothesis.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (hcomm : ¬ ∀ a b : A, a * b = b * a) :
    ∃ x : A, x ≠ 0 ∧ x * x = 0 :=
  exists_ne_zero_mul_self_eq_zero_of_not_commutative hcomm

example (hA : IsAntiliminal A) {a : A} (ha : a ≠ 0) :
    ∃ x : A, x ∈ hereditarySubalgebra a ∧ x ≠ 0 ∧ x * x = 0 :=
  hA.exists_ne_zero_mul_self_eq_zero_mem_hereditarySubalgebra ha

example [Nontrivial A] (hA : IsAntiliminal A) :
    ∃ x : A, x ≠ 0 ∧ x * x = 0 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨x, -, hx, hxx⟩ :=
    hA.exists_ne_zero_mul_self_eq_zero_mem_hereditarySubalgebra ha
  exact ⟨x, hx, hxx⟩

example (hA : IsAntiliminal A) {a : A} (ha : a ≠ 0) :
    ∃ p q : A, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧
      hereditarySubalgebra p ≤ hereditarySubalgebra a ∧
      hereditarySubalgebra q ≤ hereditarySubalgebra a ∧
      (∀ x ∈ hereditarySubalgebra p, ∀ y ∈ hereditarySubalgebra q, x * y = 0) ∧
      (∀ y ∈ hereditarySubalgebra q, ∀ x ∈ hereditarySubalgebra p, y * x = 0) :=
  hA.exists_orthogonal_hereditary_subalgebras ha

example (hA : IsAntiliminal A) {a : A} (ha : a ≠ 0) :
    ∃ p q : A, p ∈ hereditarySubalgebra a ∧ q ∈ hereditarySubalgebra a ∧
      0 ≤ p ∧ 0 ≤ q ∧ p ≠ 0 ∧ q ≠ 0 ∧ p * q = 0 ∧ q * p = 0 := by
  obtain ⟨p, q, hp, hq, hp0, hq0, hpA, hqA, hpq, hqp⟩ :=
    hA.exists_orthogonal_hereditary_subalgebras ha
  have hpP := self_mem_hereditarySubalgebra hp
  have hqQ := self_mem_hereditarySubalgebra hq
  exact ⟨p, q, hpA hpP, hqA hqQ, hp, hq, hp0, hq0,
    hpq p hpP q hqQ, hqp q hqQ p hpP⟩
