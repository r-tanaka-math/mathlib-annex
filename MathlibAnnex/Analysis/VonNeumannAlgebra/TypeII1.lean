import MathlibAnnex.Analysis.VonNeumannAlgebra.Factor
import MathlibAnnex.Analysis.VonNeumannAlgebra.Finite

/-!
# Type II₁ via finite infinite-dimensional factors

Here `IsTypeII1` uses the characterization as a nonzero finite factor whose
algebra is infinite-dimensional. Existence of a faithful normal tracial
state is a separate assertion, and is not part of the definition.
-/

set_option autoImplicit false

universe u

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A type II₁ factor, characterized as a finite infinite-dimensional
factor. The dimension condition concerns the algebra, not its representation
space. -/
def IsTypeII1 (M : VonNeumannAlgebra H) : Prop :=
  IsFactor M ∧ IsFinite M ∧ ¬ FiniteDimensional ℂ M.toStarSubalgebra

/-- A faithful tracial linear functional makes an infinite-dimensional factor type II₁. -/
theorem isTypeII1_of_isFactor_of_faithful_tracial
    (M : VonNeumannAlgebra H) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (htrace : ∀ a : H →L[ℂ] H, a ∈ M →
      ∀ b : H →L[ℂ] H, b ∈ M → φ (a * b) = φ (b * a))
    (hfaithful : ∀ a : H →L[ℂ] H, a ∈ M →
      φ (star a * a) = 0 → a = 0)
    (hfactor : IsFactor M)
    (hinfinite : ¬ FiniteDimensional ℂ M.toStarSubalgebra) : IsTypeII1 M :=
  ⟨hfactor, isFinite_of_faithful_tracial M φ htrace hfaithful, hinfinite⟩

/-- Finite-dimensional factors are excluded from type II₁. -/
theorem not_isTypeII1_of_finiteDimensional (M : VonNeumannAlgebra H)
    [FiniteDimensional ℂ M.toStarSubalgebra] : ¬ IsTypeII1 M := by
  intro hM
  exact hM.2.2 inferInstance

end VonNeumannAlgebra
