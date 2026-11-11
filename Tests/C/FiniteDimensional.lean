import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.FiniteDimensional

/-!
Typed consumers for finite-dimensional algebra projection minimization and
the accepted II₁ characterization. Every dimension assumption below refers
to the algebra subtype; the ambient Hilbert space remains arbitrary.
-/

set_option autoImplicit false
noncomputable section

open VonNeumannAlgebra
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsMinimalStarProjection q ∧ q ≤ p :=
  exists_isMinimalStarProjection_le_of_finiteDimensional M hp hp0

example (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    [Nontrivial M.toStarSubalgebra] :
    ∃ p : M.toStarSubalgebra, IsMinimalStarProjection p :=
  exists_isMinimalStarProjection_of_finiteDimensional M

example (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    (hfactor : IsFactor M) :
    ∃ p : M.toStarSubalgebra, IsMinimalStarProjection p := by
  have hone : (1 : M.toStarSubalgebra) ≠ 0 := fun h ↦
    hfactor.1 (congrArg Subtype.val h)
  letI : Nontrivial M.toStarSubalgebra := ⟨⟨1, 0, hone⟩⟩
  exact exists_isMinimalStarProjection_of_finiteDimensional M

example (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsMinimalStarProjection p) : IsAbelianProjection M p :=
  isAbelianProjection_of_isMinimalStarProjection M hp

example (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsMinimalStarProjection p) :
    ∀ a b : corner M p hp.1, a * b = b * a :=
  (isAbelianProjection_iff_corner_commutative M p hp.1).mp
    (isAbelianProjection_of_isMinimalStarProjection M hp)

example (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra]
    [Nontrivial M.toStarSubalgebra] :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 :=
  exists_isAbelianProjection_ne_zero_of_finiteDimensional M

example (M : VonNeumannAlgebra H) [FiniteDimensional ℂ M.toStarSubalgebra] :
    IsTypeI M :=
  isTypeI_of_finiteDimensional M

/-- The type I consequence retains the permitted zero-algebra case. -/
example (M : VonNeumannAlgebra H) [Subsingleton M.toStarSubalgebra]
    [FiniteDimensional ℂ M.toStarSubalgebra] : IsTypeI M :=
  isTypeI_of_finiteDimensional M

example (M : VonNeumannAlgebra H) [Nontrivial M.toStarSubalgebra] (hII : IsTypeII M) :
    ¬ FiniteDimensional ℂ M.toStarSubalgebra :=
  hII.not_finiteDimensional

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (hfinite : IsFinite M) (hII : IsTypeII M) : IsTypeII1 M :=
  isTypeII1_of_isFactor_of_isFinite_of_isTypeII M hfactor hfinite hII

example (M : VonNeumannAlgebra H) :
    IsTypeII1 M ↔ IsFactor M ∧ IsFinite M ∧ IsTypeII M :=
  isTypeII1_iff_isFactor_and_isFinite_and_isTypeII M

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M) (hfinite : IsFinite M) :
    IsTypeII1 M ↔ IsTypeII M :=
  isTypeII1_iff_isTypeII_of_isFactor_of_isFinite M hfactor hfinite

/-- The forward direction remains the pre-existing fixed supply theorem. -/
example (M : VonNeumannAlgebra H) (hII₁ : IsTypeII1 M) : IsTypeII M :=
  hII₁.isTypeII

