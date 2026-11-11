import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.Basic

set_option autoImplicit false
noncomputable section

open VonNeumannAlgebra
open scoped CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Arbitrary index types, in an independent universe, have internal
projection suprema and infima. No countability instance is used. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    ∃ lo hi : M.toStarSubalgebra,
      IsStarProjection lo ∧ IsStarProjection hi ∧
      (∀ i, lo ≤ p i ∧ p i ≤ hi) ∧
      (∀ q : M.toStarSubalgebra, IsStarProjection q →
        (∀ i, q ≤ p i) → q ≤ lo) ∧
      (∀ q : M.toStarSubalgebra, IsStarProjection q →
        (∀ i, p i ≤ q) → hi ≤ q) := by
  refine ⟨iInfProjection M p hp, iSupProjection M p hp,
    isStarProjection_iInfProjection M p hp, isStarProjection_iSupProjection M p hp, ?_, ?_, ?_⟩
  · exact fun i ↦ ⟨iInfProjection_le M p hp i, le_iSupProjection M p hp i⟩
  · exact fun q hq hle ↦ le_iInfProjection M p hp hq hle
  · exact fun q hq hle ↦ iSupProjection_le M p hp hq hle

/-- The supremum's range is the closed linear span of all the ranges,
even when the family is not orthogonal. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i)) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (q : H →L[ℂ] H).range =
        (⨆ i, (p i : H →L[ℂ] H).range).topologicalClosure := by
  exact ⟨iSupProjection M p hp, isStarProjection_iSupProjection M p hp,
    range_iSupProjection M p hp⟩

/-- Order on internal projections is faithfully represented by range
inclusion, without treating arbitrary operators as a lattice. -/
example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hrange : (p : H →L[ℂ] H).range ≤ (q : H →L[ℂ] H).range) :
    q * p = p ∧ p * q = p := by
  have hle := (projection_le_iff_range_le M hp hq).2 hrange
  exact ⟨(hp.le_iff_mul_eq_right hq).1 hle, (hp.le_iff_mul_eq_left hq).1 hle⟩

/-- The empty family is allowed by both set-level existence theorems. -/
example (M : VonNeumannAlgebra H) :
    (∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → q ≤ r) ∧
    (∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → r ≤ q) := by
  obtain ⟨lo, hlo, _, hleast⟩ :=
    exists_projection_sup M ∅ (fun p hp ↦ False.elim hp)
  obtain ⟨hi, hhi, _, hgreatest⟩ :=
    exists_projection_inf M ∅ (fun p hp ↦ False.elim hp)
  constructor
  · exact ⟨lo, hlo, fun r hr ↦ hleast r hr (fun p hp ↦ False.elim hp)⟩
  · exact ⟨hi, hhi, fun r hr ↦ hgreatest r hr (fun p hp ↦ False.elim hp)⟩
