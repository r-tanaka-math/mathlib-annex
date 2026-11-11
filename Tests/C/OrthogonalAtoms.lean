import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.OrthogonalAtoms

set_option autoImplicit false
noncomputable section

open VonNeumannAlgebra
open scoped CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed minimal projection is the common initial projection of a
nonempty family of internal witnesses, with zero off-diagonal products. -/
example (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (p : M.toStarSubalgebra)
    (hp : MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p) :
    ∃ s : Set M.toStarSubalgebra, p ∈ s ∧
      (∀ v ∈ s, v * star v * v = v ∧ star v * v = p) ∧
      s.Pairwise (fun v w ↦ star v * w = 0) := by
  obtain ⟨s, hps, hs, horth, _⟩ :=
    hM.exists_orthogonal_partial_isometries_of_minimal_projection hp
  refine ⟨s, hps, hs, ?_⟩
  intro v hv w hw hne
  exact (hs v hv).1.star_mul_eq_zero_of_final_mul_final_eq_zero
    (hs w hw).1 (horth hv hw hne)

/-- Exhaustion by the final projections means their represented ranges
span densely. The index is a set subtype, with no countability instance. -/
example (M : VonNeumannAlgebra H) (hM : IsFactor M)
    (p : M.toStarSubalgebra)
    (hp : MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p) :
    ∃ s : Set M.toStarSubalgebra, s.Nonempty ∧
      (⨆ v : s,
        (((v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra)) : H →L[ℂ] H).range
      ).topologicalClosure = ⊤ := by
  obtain ⟨s, hps, hs, _, hsup⟩ :=
    hM.exists_orthogonal_partial_isometries_of_minimal_projection hp
  refine ⟨s, ⟨p, hps⟩, ?_⟩
  let f : s → M.toStarSubalgebra := fun v ↦ v.1 * star v.1
  have hf (v : s) : IsStarProjection (f v) :=
    (hs v.1 v.2).1.isStarProjection_mul_star_self
  change (⨆ v : s, (f v : H →L[ℂ] H).range).topologicalClosure = ⊤
  rw [← range_iSupProjection M f hf]
  change iSupProjection M f hf = 1 at hsup
  rw [hsup]
  ext ξ
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨ξ, rfl⟩

/-- The type I factor endpoint supplies genuinely minimal abelian final
projections; nonzero is included in the reused minimality predicate. -/
example (M : VonNeumannAlgebra H) (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ s : Set M.toStarSubalgebra, s.Nonempty ∧
      ∀ v ∈ s, IsAbelianProjection M (v * star v) ∧
        MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection (v * star v) := by
  obtain ⟨p, _, _, s, hps, _, _, hminimal, _⟩ :=
    hM.exists_orthogonal_abelian_atoms hI
  exact ⟨s, ⟨p, hps⟩, hminimal⟩
