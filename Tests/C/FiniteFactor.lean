import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.FiniteFactor

/-!
Typed consumers for the arbitrary-dimensional proper-isometry construction,
finite type I factor theorem, and accepted II₁ to general type II bridge.
These consumers use the finite-factor results directly.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (hdim : ¬ FiniteDimensional ℂ H) :
    ∃ v : H →L[ℂ] H, star v * v = 1 ∧ v * star v ≠ 1 :=
  ContinuousLinearMap.exists_proper_isometry_of_not_finiteDimensional ℂ H hdim

example (hfinite : ∀ v : H →L[ℂ] H, star v * v = 1 → v * star v = 1) :
    FiniteDimensional ℂ H :=
  ContinuousLinearMap.finiteDimensional_of_isometries_unitary ℂ H hfinite

example (M : VonNeumannAlgebra H) (hfinite : M.IsFinite)
    (hfull : ∀ T : H →L[ℂ] H, T ∈ M) : FiniteDimensional ℂ H :=
  VonNeumannAlgebra.finiteDimensional_of_isFinite_of_all_operators_mem M hfinite hfull

example (M : VonNeumannAlgebra H) (hfinite : M.IsFinite)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : FiniteDimensional ℂ K :=
  hfinite.finiteDimensional_of_starAlgEquiv_continuousLinearMap e

example (M : VonNeumannAlgebra H) (hfactor : M.IsFactor)
    (hfinite : M.IsFinite) (htype : M.IsTypeI) :
    FiniteDimensional ℂ M.toStarSubalgebra :=
  VonNeumannAlgebra.finiteDimensional_of_isFactor_of_isFinite_of_isTypeI
    M hfactor hfinite htype

example (M : VonNeumannAlgebra H) (hII₁ : M.IsTypeII1) : ¬ M.IsTypeI :=
  hII₁.not_isTypeI

example (M : VonNeumannAlgebra H) (hII₁ : M.IsTypeII1)
    (p : M.toStarSubalgebra) (hp : VonNeumannAlgebra.IsAbelianProjection M p) : p = 0 :=
  hII₁.eq_zero_of_abelian_projection hp

example (M : VonNeumannAlgebra H) (hII₁ : M.IsTypeII1) : M.IsTypeII :=
  hII₁.isTypeII

example (M : VonNeumannAlgebra H) (hII₁ : M.IsTypeII1) :
    M.IsTypeII ∧ IsFiniteProjection (1 : M.toStarSubalgebra) :=
  ⟨hII₁.isTypeII,
    (VonNeumannAlgebra.isFinite_iff_isFiniteProjection_one M).mp hII₁.2.1⟩

