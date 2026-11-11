/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryBinaryTree

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (hA : IsAntiliminal A) {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ f : List Bool → A, f [] = a ∧
      (∀ s, 0 ≤ f s ∧ f s ≠ 0) ∧
      (∀ s t, s.length = t.length → s ≠ t → f s * f t = 0) := by
  obtain ⟨f, hroot, hpositive, _hchild, _hsplit, hlevel⟩ :=
    hA.exists_hereditary_binary_tree ha ha0
  refine ⟨f, hroot, hpositive, ?_⟩
  intro s t hlen hne
  exact hlevel s t hlen hne (f s)
    (self_mem_hereditarySubalgebra (hpositive s).1) (f t)
    (self_mem_hereditarySubalgebra (hpositive t).1)

example (hA : IsAntiliminal A) {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ f : List Bool → A, f [] = a ∧
      (∀ s, f s ≠ 0) ∧
      (∀ s b, hereditarySubalgebra (f (b :: s)) ≤ hereditarySubalgebra (f s)) := by
  obtain ⟨f, hroot, hpositive, hchild, _hsplit, _hlevel⟩ :=
    hA.exists_hereditary_binary_tree ha ha0
  exact ⟨f, hroot, fun s => (hpositive s).2, hchild⟩

end MathlibAnnex.Analysis.CStarAlgebra
