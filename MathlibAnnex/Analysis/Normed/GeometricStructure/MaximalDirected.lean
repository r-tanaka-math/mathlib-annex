/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.PreorderFilter

/-!
# Maximal directed subsets of the orthogonality preorder

This proves the standalone characterization in Lemma 3.3 of
J. Math. Anal. Appl. 514 (2022), 126307. It is not inferred from the later
filter/face or antichain endpoints. The proof uses the existing maximal-filter
extension theorem with the directed superset as its starting set.

Completeness and nontriviality are unnecessary. The directed predicate below
allows the empty set; the reverse implication proves nonemptiness by testing
the singleton `{0}`. Thus no missing empty case is hidden in the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Set

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A maximal order filter is exactly a maximal downward directed subset of the
orthogonality preorder. The right side does not assume upward closure or nonemptiness. -/
theorem isMaximalBirkhoffJamesFilter_iff_maximal_directed (U : Set E) :
    IsMaximalBirkhoffJamesFilter 𝕜 U ↔
      Maximal (fun D : Set E => ∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D,
        birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
        birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y) U := by
  classical
  constructor
  · intro hU
    refine ⟨fun x hx y hy => hU.1.directed 𝕜 hx hy, ?_⟩
    intro D hD hUD
    obtain ⟨V, hDV, hV⟩ := exists_isMaximalBirkhoffJamesFilter_of_directed 𝕜
      ((hU.1.nonempty 𝕜).mono hUD) hD
    exact hDV.trans (hU.2 hV.1 (hUD.trans hDV))
  · intro hU
    have hne : U.Nonempty := by
      by_contra hne
      have hempty : U = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun x hx => hne ⟨x, hx⟩)
      have hsingle : ∀ x ∈ ({0} : Set E), ∀ y ∈ ({0} : Set E),
          ∃ z ∈ ({0} : Set E),
            birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
            birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y := by
        rintro x rfl y rfl
        exact ⟨0, Set.mem_singleton 0, Set.Subset.rfl, Set.Subset.rfl⟩
      have hsub : U ⊆ ({0} : Set E) := by rw [hempty]; exact Set.empty_subset _
      exact hne ⟨0, hU.2 hsingle hsub (Set.mem_singleton 0)⟩
    obtain ⟨V, hUV, hV⟩ := exists_isMaximalBirkhoffJamesFilter_of_directed 𝕜 hne hU.1
    have hVU : V ⊆ U := hU.2 (fun x hx y hy => hV.1.directed 𝕜 hx hy) hUV
    have heq : U = V := Set.Subset.antisymm hUV hVU
    rw [heq]
    exact hV

end NormedSpace
