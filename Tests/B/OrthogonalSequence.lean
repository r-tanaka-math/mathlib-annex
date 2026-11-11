import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalSequence

set_option autoImplicit false
open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (p : ℕ → H →L[ℂ] H) (hp : ∀ n, IsStarProjection (p n))
    (horth : Pairwise (fun i j ↦ p i * p j = 0)) :
    ContinuousLinearMap.StronglyConverges p atTop 0 :=
  ContinuousLinearMap.stronglyConverges_zero_of_pairwise_orthogonal_projections p hp horth

example (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsMinimalStarProjection p) : M.IsAbelianProjection p :=
  M.isAbelianProjection_of_isMinimalStarProjection hp

example (M : VonNeumannAlgebra H) (hM : M.IsTypeII1) (p : M.toStarSubalgebra) :
    ¬ IsMinimalStarProjection p := hM.not_isMinimalStarProjection p

example (M : VonNeumannAlgebra H)
    (hM : ∀ r : M.toStarSubalgebra, ¬ IsMinimalStarProjection r)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → M.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≠ 0 ∧ q n ≤ p) ∧
      Pairwise (fun i j ↦ q i * q j = 0) :=
  M.exists_orthogonal_sequence_of_no_minimal_projection hM hp hp0

example (M : VonNeumannAlgebra H) (hM : M.IsTypeII1)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → M.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≤ p ∧ ‖q n‖ = 1) ∧
      Pairwise (fun i j ↦ q i * q j = 0) ∧
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (q n : H →L[ℂ] H)) atTop 0 :=
  hM.exists_stronglyConverges_zero_projection_sequence hp hp0
