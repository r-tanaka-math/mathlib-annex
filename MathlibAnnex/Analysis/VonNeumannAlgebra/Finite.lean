import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Unitary

/-!
# Finite von Neumann algebras and faithful traces

Finiteness of the unit means that an isometry in the algebra is unitary.
The trace argument is algebraic: the defect `1 - v * star v` is a star
projection with trace zero. Faithfulness on star-squares annihilates this
defect. Neither continuity nor normality is needed for this implication.
-/

set_option autoImplicit false

universe u

namespace LinearMap

variable {A : Type u} [Ring A] [Algebra ℂ A] [StarRing A]

/-- A faithful tracial linear functional rules out a proper isometry.

Faithfulness is required on every star-square. Normalization and positivity
are unnecessary for this purely algebraic consequence. -/
theorem mul_star_self_eq_one_of_faithful_tracial
    (φ : A →ₗ[ℂ] ℂ)
    (htrace : ∀ a b : A, φ (a * b) = φ (b * a))
    (hfaithful : ∀ a : A, φ (star a * a) = 0 → a = 0)
    {v : A} (hv : star v * v = 1) : v * star v = 1 := by
  have hvv : IsStarProjection (v * star v) := by
    refine ⟨?_, IsSelfAdjoint.mul_star_self v⟩
    change (v * star v) * (v * star v) = v * star v
    calc
      (v * star v) * (v * star v) = v * (star v * v) * star v := by
        simp only [mul_assoc]
      _ = v * star v := by rw [hv, mul_one]
  let p : A := 1 - v * star v
  have hp : IsStarProjection p := hvv.one_sub
  have hφp : φ p = 0 := by
    dsimp [p]
    rw [map_sub, htrace v (star v), hv, sub_self]
  have hp0 : p = 0 := hfaithful p (by
    rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    exact hφp)
  exact (sub_eq_zero.mp hp0).symm

end LinearMap

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The unit of a von Neumann algebra is finite: every isometry belonging
to the algebra is a unitary. -/
def IsFinite (M : VonNeumannAlgebra H) : Prop :=
  ∀ v : H →L[ℂ] H, v ∈ M → star v * v = 1 → v * star v = 1

/-- A faithful trace on a von Neumann algebra makes its unit finite.

The functional is defined on ambient operators; traciality and faithfulness
are used only on `M`. In particular, a faithful tracial state satisfies the
hypotheses, without requiring normality for this implication. -/
theorem isFinite_of_faithful_tracial
    (M : VonNeumannAlgebra H) (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (htrace : ∀ a : H →L[ℂ] H, a ∈ M →
      ∀ b : H →L[ℂ] H, b ∈ M → φ (a * b) = φ (b * a))
    (hfaithful : ∀ a : H →L[ℂ] H, a ∈ M →
      φ (star a * a) = 0 → a = 0) : IsFinite M := by
  intro v hv hvisometry
  let ψ : M.toStarSubalgebra →ₗ[ℂ] ℂ :=
    φ.comp M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
  let w : M.toStarSubalgebra := ⟨v, hv⟩
  have hw : star w * w = 1 := Subtype.ext hvisometry
  have hψtrace : ∀ a b : M.toStarSubalgebra, ψ (a * b) = ψ (b * a) := by
    intro a b
    exact htrace a a.property b b.property
  have hψfaithful : ∀ a : M.toStarSubalgebra, ψ (star a * a) = 0 → a = 0 := by
    intro a ha
    exact Subtype.ext (hfaithful a a.property ha)
  have hunitary := ψ.mul_star_self_eq_one_of_faithful_tracial hψtrace hψfaithful hw
  exact congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H)) hunitary

/-- Finiteness supplies the second equation in the standard unitary
membership predicate. -/
theorem IsFinite.mem_unitary {M : VonNeumannAlgebra H} (hM : IsFinite M)
    {v : H →L[ℂ] H} (hv : v ∈ M) (hvisometry : star v * v = 1) :
    v ∈ unitary (H →L[ℂ] H) :=
  Unitary.mem_iff.mpr ⟨hvisometry, hM v hv hvisometry⟩

/-- Every commutative von Neumann algebra is finite. This assertion does
not impose factorality or finite dimensionality. -/
theorem isFinite_of_commutative (M : VonNeumannAlgebra H)
    (hcomm : ∀ a : H →L[ℂ] H, a ∈ M →
      ∀ b : H →L[ℂ] H, b ∈ M → a * b = b * a) : IsFinite M := by
  intro v hv hvisometry
  exact (hcomm v hv (star v) (star_mem hv)).trans hvisometry

end VonNeumannAlgebra
