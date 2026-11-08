import MathlibAnnex.Analysis.VonNeumannAlgebra.NormalFunctional

set_option autoImplicit false

open Filter Set Topology
open scoped InnerProduct ComplexOrder

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The index is an arbitrary directed preorder in an independent universe. -/
example {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (f : ι → H →L[ℂ] H) (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i)
    (hnorm : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) (ξ : H) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ IsLUB (Set.range f) T ∧
      ContinuousLinearMap.StronglyConverges f atTop T ∧
      IsLUB (Set.range (fun i ↦ (inner ℂ ξ (f i ξ)).re)) (inner ℂ ξ (T ξ)).re := by
  obtain ⟨T, hTpos, hTlub, hTlim⟩ :=
    ContinuousLinearMap.exists_isLUB_stronglyConverges_of_monotone f hmono hpos hnorm
  exact ⟨T, hTpos, hTlub, hTlim,
    ContinuousLinearMap.isLUB_re_inner_of_monotone_of_stronglyConverges hmono hTlim ξ⟩

/-- Set-indexed positive families receive an actual supremum witness. -/
example (s : Set (H →L[ℂ] H)) (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ T ∈ s, 0 ≤ T) (hbdd : BddAbove s) :
    ∃ T : H →L[ℂ] H, 0 ≤ T ∧ IsLUB s T := by
  obtain ⟨T, hTpos, hTlub, _⟩ :=
    ContinuousLinearMap.exists_isLUB_stronglyConverges_of_directedOn s hne hdir hpos hbdd
  exact ⟨T, hTpos, hTlub⟩

/-- The normality predicate quantifies over sets of elements of the algebra,
and not merely over sequences of ambient operators. -/
example (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hφ : M.IsNormalPositiveFunctional φ) (s : Set M.toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ T ∈ s, 0 ≤ T)
    (hbdd : BddAbove s) (T : M.toStarSubalgebra) (hT : IsLUB s T) :
    IsLUB ((fun S ↦ (φ S).re) '' s) (φ T).re :=
  hφ.2 s hne hdir hpos hbdd T hT
