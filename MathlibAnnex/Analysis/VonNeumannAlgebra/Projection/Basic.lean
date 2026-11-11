/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.InnerProductSpace.StarOrder
import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated

/-!
# Suprema and infima of projections in a concrete von Neumann algebra

The supremum of an arbitrary family is the orthogonal projection onto the
closed linear span of its ranges. Invariance under the commutant proves that
this projection belongs to the specified algebra. The construction uses the
existing `IsStarProjection` predicate and leaves all nonprojections outside
the projection order statements.
Infima are obtained by taking complements of the suprema of complements.
-/

set_option autoImplicit false
noncomputable section

open ContinuousLinearMap
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An invariant closed subspace determines a projection in the given
algebra. The membership conclusion is in `M`, not merely in `B(H)`. -/
theorem starProjection_mem (M : VonNeumannAlgebra H)
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (hK : ∀ y : H →L[ℂ] H, y ∈ M.commutant →
      K ∈ Module.End.invtSubmodule y) : K.starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    (isStarProjection_starProjection (U := K)) M).2
  simpa only [Submodule.range_starProjection] using hK

/-- Projection order in the algebra is inclusion of the represented
ranges. Both directions retain the original subtype carrier. -/
theorem projection_le_iff_range_le (M : VonNeumannAlgebra H)
    {p q : M.toStarSubalgebra} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    p ≤ q ↔ (p : H →L[ℂ] H).range ≤ (q : H →L[ℂ] H).range := by
  letI : StarOrderedRing M.toStarSubalgebra := Subtype.starOrderedRing (𝕜 := ℂ) _
  rw [hp.le_iff_mul_eq_right hq]
  constructor
  · intro h
    rintro ξ ⟨η, rfl⟩
    refine ⟨(p : H →L[ℂ] H) η, ?_⟩
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) η) h
  · intro h
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    obtain ⟨η, hη⟩ := h (show (p : H →L[ℂ] H) ξ ∈
      (p : H →L[ℂ] H).range from ⟨ξ, rfl⟩)
    change (q : H →L[ℂ] H) ((p : H →L[ℂ] H) ξ) = (p : H →L[ℂ] H) ξ
    rw [← hη]
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H) η)
      hq.isIdempotentElem.eq

/-- Closed spans of arbitrary families of commutant-invariant subspaces
again have their orthogonal projections in the algebra. -/
theorem starProjection_closure_iSup_mem (M : VonNeumannAlgebra H)
    {ι : Type v} (K : ι → Submodule ℂ H)
    (hK : ∀ i, ∀ y : H →L[ℂ] H, y ∈ M.commutant →
      K i ∈ Module.End.invtSubmodule y) :
    (⨆ i, K i).topologicalClosure.starProjection ∈ M := by
  apply starProjection_mem
  intro y hy
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
  apply iSup_le
  intro i
  exact ((Module.End.mem_invtSubmodule_iff_map_le y).1 (hK i y hy)).trans
    (le_iSup K i)

/-- The supremum of any family of projections, realized inside the same
von Neumann algebra. The index universe is independent of that of `H`. -/
def iSupProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    M.toStarSubalgebra :=
  ⟨(⨆ i, (p i : H →L[ℂ] H).range).topologicalClosure.starProjection,
    starProjection_closure_iSup_mem M
      (fun i ↦ (p i : H →L[ℂ] H).range) (fun i ↦ by
        exact (VonNeumannAlgebra.IsStarProjection.mem_iff
          ((hp i).map M.toStarSubalgebra.subtype) M).1 (p i).property)⟩

/-- The constructed supremum is a star projection. -/
theorem isStarProjection_iSupProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    IsStarProjection (iSupProjection M p hp) := by
  have h := isStarProjection_starProjection
    (U := (⨆ i, (p i : H →L[ℂ] H).range).topologicalClosure)
  constructor
  · apply Subtype.ext
    exact h.isIdempotentElem.eq
  · apply Subtype.ext
    exact h.isSelfAdjoint.star_eq

/-- The range formula makes the closed-span construction explicit. -/
@[simp]
theorem range_iSupProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    (iSupProjection M p hp : H →L[ℂ] H).range =
      (⨆ i, (p i : H →L[ℂ] H).range).topologicalClosure := by
  exact Submodule.range_starProjection _

/-- Every member lies below the constructed supremum. -/
theorem le_iSupProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) (i : ι) :
    p i ≤ iSupProjection M p hp := by
  apply (projection_le_iff_range_le M (hp i) (isStarProjection_iSupProjection M p hp)).2
  rw [range_iSupProjection]
  exact (le_iSup (fun i ↦ (p i : H →L[ℂ] H).range) i).trans
    (Submodule.le_topologicalClosure _)

/-- Leastness among projection upper bounds. This does not assert an
unrestricted least upper bound in the nonlattice order on all operators. -/
theorem iSupProjection_le (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q) (hle : ∀ i, p i ≤ q) :
    iSupProjection M p hp ≤ q := by
  apply (projection_le_iff_range_le M (isStarProjection_iSupProjection M p hp) hq).2
  rw [range_iSupProjection]
  apply Submodule.topologicalClosure_minimal
  · exact iSup_le fun i ↦ (projection_le_iff_range_le M (hp i) hq).1 (hle i)
  · exact (hq.map M.toStarSubalgebra.subtype).isIdempotentElem.isClosed_range

/-- Every set of projections has a least projection upper bound, including
the empty set and arbitrary uncountable sets. -/
theorem exists_projection_sup (M : VonNeumannAlgebra H)
    (s : Set M.toStarSubalgebra) (hs : ∀ p ∈ s, IsStarProjection p) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ p ∈ s, p ≤ q) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r →
        (∀ p ∈ s, p ≤ r) → q ≤ r := by
  let p : s → M.toStarSubalgebra := fun x ↦ x.1
  have hp : ∀ x, IsStarProjection (p x) := fun x ↦ hs x.1 x.2
  refine ⟨iSupProjection M p hp, isStarProjection_iSupProjection M p hp, ?_, ?_⟩
  · intro x hx
    exact le_iSupProjection M p hp ⟨x, hx⟩
  · intro r hr hbound
    exact iSupProjection_le M p hp hr (fun x ↦ hbound x.1 x.2)

/-- The supremum is independent of a second projection satisfying the
same two order properties. -/
theorem iSupProjection_unique (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hupper : ∀ i, p i ≤ q)
    (hleast : ∀ r : M.toStarSubalgebra, IsStarProjection r →
      (∀ i, p i ≤ r) → q ≤ r) : q = iSupProjection M p hp := by
  apply le_antisymm
  · exact hleast _ (isStarProjection_iSupProjection M p hp) (le_iSupProjection M p hp)
  · exact iSupProjection_le M p hp hq hupper

/-- The infimum of an arbitrary family of projections, obtained by
complementing the supremum of the complementary family. -/
def iInfProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    M.toStarSubalgebra :=
  1 - iSupProjection M (fun i ↦ 1 - p i) (fun i ↦ (hp i).one_sub)

theorem isStarProjection_iInfProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    IsStarProjection (iInfProjection M p hp) :=
  (isStarProjection_iSupProjection M (fun i ↦ 1 - p i) (fun i ↦ (hp i).one_sub)).one_sub

/-- The constructed infimum is below every member of the family. -/
theorem iInfProjection_le (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) (i : ι) :
    iInfProjection M p hp ≤ p i := by
  have h := sub_le_sub_left
    (le_iSupProjection M (fun i ↦ 1 - p i) (fun i ↦ (hp i).one_sub) i) 1
  simpa only [iInfProjection, sub_sub_cancel] using h

/-- Greatestness among projection lower bounds. -/
theorem le_iInfProjection (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q) (hle : ∀ i, q ≤ p i) :
    q ≤ iInfProjection M p hp := by
  have h := iSupProjection_le M (fun i ↦ 1 - p i)
    (fun i ↦ (hp i).one_sub) hq.one_sub (fun i ↦ sub_le_sub_left (hle i) 1)
  simpa only [iInfProjection, sub_sub_cancel] using sub_le_sub_left h 1

/-- Every set of projections has a greatest projection lower bound. -/
theorem exists_projection_inf (M : VonNeumannAlgebra H)
    (s : Set M.toStarSubalgebra) (hs : ∀ p ∈ s, IsStarProjection p) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ p ∈ s, q ≤ p) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r →
        (∀ p ∈ s, r ≤ p) → r ≤ q := by
  let p : s → M.toStarSubalgebra := fun x ↦ x.1
  have hp : ∀ x, IsStarProjection (p x) := fun x ↦ hs x.1 x.2
  refine ⟨iInfProjection M p hp, isStarProjection_iInfProjection M p hp, ?_, ?_⟩
  · intro x hx
    exact iInfProjection_le M p hp ⟨x, hx⟩
  · intro r hr hbound
    exact le_iInfProjection M p hp hr (fun x ↦ hbound x.1 x.2)

/-- The infimum is uniquely determined by its projection order
properties. -/
theorem iInfProjection_unique (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hlower : ∀ i, q ≤ p i)
    (hgreatest : ∀ r : M.toStarSubalgebra, IsStarProjection r →
      (∀ i, r ≤ p i) → r ≤ q) : q = iInfProjection M p hp := by
  apply le_antisymm
  · exact le_iInfProjection M p hp hq hlower
  · exact hgreatest _ (isStarProjection_iInfProjection M p hp) (iInfProjection_le M p hp)

end VonNeumannAlgebra
