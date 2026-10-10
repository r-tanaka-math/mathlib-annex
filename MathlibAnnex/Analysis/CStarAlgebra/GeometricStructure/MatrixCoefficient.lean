import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# Matrix coefficients of possibly nonunital C-star representations

This file uses the existing `NonUnitalCStarRepresentation` interface for genuinely
nonunital algebras. It does not use the different interface `NonUnitalRepresentation`,
whose domain is unital. The map to operators is contractive by Mathlib's theorem,
not by an additional hypothesis.

No nonzeroness, irreducibility, separability, or finite dimension is assumed in the
coefficient construction. A unit vector alone does not make a coefficient a
norm-one functional for an arbitrary representation. In particular, no such
norm equality is asserted for a zero representation.
-/

set_option autoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace NonUnitalCStarRepresentation

private def coefficientContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The pullback of an operator matrix coefficient along an existing representation. -/
def matrixCoefficient (pi : NonUnitalCStarRepresentation A H) (x y : H) : A →L[ℂ] ℂ :=
  (InnerProductSpace.matrixCoefficient ℂ x y).comp (coefficientContinuousMap pi)

@[simp]
theorem matrixCoefficient_apply (pi : NonUnitalCStarRepresentation A H) (x y : H) (a : A) :
    matrixCoefficient pi x y a = inner ℂ y (pi a x) := rfl

theorem norm_matrixCoefficient_apply_le (pi : NonUnitalCStarRepresentation A H)
    (x y : H) (a : A) :
    ‖matrixCoefficient pi x y a‖ ≤ (‖x‖ * ‖y‖) * ‖a‖ := by
  calc
    ‖matrixCoefficient pi x y a‖ ≤
        ‖InnerProductSpace.matrixCoefficient ℂ x y‖ * ‖pi a‖ :=
      (InnerProductSpace.matrixCoefficient ℂ x y).le_opNorm (pi a)
    _ = (‖x‖ * ‖y‖) * ‖pi a‖ := by rw [InnerProductSpace.norm_matrixCoefficient]
    _ ≤ (‖x‖ * ‖y‖) * ‖a‖ :=
      mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le pi a)
        (mul_nonneg (norm_nonneg x) (norm_nonneg y))

theorem norm_matrixCoefficient_le (pi : NonUnitalCStarRepresentation A H) (x y : H) :
    ‖matrixCoefficient pi x y‖ ≤ ‖x‖ * ‖y‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))
    (norm_matrixCoefficient_apply_le pi x y)

/-- The functional kernel is a pullback, not the kernel of the representation. -/
theorem ker_matrixCoefficient (pi : NonUnitalCStarRepresentation A H) (x y : H) :
    (matrixCoefficient pi x y).ker =
      (InnerProductSpace.matrixCoefficient ℂ x y).ker.comap
        (coefficientContinuousMap pi).toLinearMap :=
  InnerProductSpace.ker_matrixCoefficient_comp (coefficientContinuousMap pi) x y

@[simp]
theorem mem_ker_matrixCoefficient_iff
    (pi : NonUnitalCStarRepresentation A H) (x y : H) (a : A) :
    a ∈ (matrixCoefficient pi x y).ker ↔ inner ℂ y (pi a x) = 0 := Iff.rfl

/-- Adjoints exchange the two vectors and conjugate the scalar value. -/
theorem matrixCoefficient_star (pi : NonUnitalCStarRepresentation A H)
    (x y : H) (a : A) :
    matrixCoefficient pi x y (star a) = star (matrixCoefficient pi y x a) := by
  change inner ℂ y (pi (star a) x) = star (inner ℂ x (pi a y))
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact InnerProductSpace.matrixCoefficient_apply_adjoint (pi a) y x

/-- The full two-vector Gram identity; positivity is not an extra premise. -/
theorem matrixCoefficient_star_mul (pi : NonUnitalCStarRepresentation A H)
    (x y : H) (a b : A) :
    matrixCoefficient pi x y (star a * b) = inner ℂ (pi a y) (pi b x) := by
  change inner ℂ y (pi (star a * b) x) = _
  rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right (pi a) y (pi b x)

theorem matrixCoefficient_star_mul_self (pi : NonUnitalCStarRepresentation A H)
    (x : H) (a : A) :
    matrixCoefficient pi x x (star a * a) = (‖pi a x‖ : ℂ) ^ 2 := by
  rw [matrixCoefficient_star_mul, inner_self_eq_norm_sq_to_K]
  rfl

/-- An actual unitary intertwiner transports coefficients exactly. -/
theorem matrixCoefficient_eq_of_intertwines
    (pi : NonUnitalCStarRepresentation A H) (rho : NonUnitalCStarRepresentation A K)
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ (a : A) (z : H), U (pi a z) = rho a (U z))
    (x y : H) :
    matrixCoefficient rho (U x) (U y) = matrixCoefficient pi x y := by
  ext a
  change inner ℂ (U y) (rho a (U x)) = inner ℂ y (pi a x)
  rw [← hU a x, U.inner_map_map]

theorem exists_matrixCoefficient_eq_of_unitaryEquivalent
    {pi : NonUnitalCStarRepresentation A H} {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) (x y : H) :
    ∃ u v : K, ‖u‖ = ‖x‖ ∧ ‖v‖ = ‖y‖ ∧
      matrixCoefficient rho u v = matrixCoefficient pi x y := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U x, U y, U.norm_map x, U.norm_map y,
    matrixCoefficient_eq_of_intertwines pi rho U hU x y⟩

/-- Restricting the canonical unitization representation recovers the same coefficient. -/
theorem matrixCoefficient_unitization_inr
    (pi : NonUnitalCStarRepresentation A H) (x y : H) (a : A) :
    matrixCoefficient pi.unitization.toNonUnitalStarAlgHom x y (Unitization.inr a) =
      matrixCoefficient pi x y a := by
  change inner ℂ y (pi.unitization (Unitization.inr a) x) = inner ℂ y (pi a x)
  rw [unitization_inr]

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal specialization agrees with the already existing vector functional. -/
theorem Representation.matrixCoefficient_self_eq_vectorFunctional
    (pi : Representation A H) (x : H) :
    NonUnitalCStarRepresentation.matrixCoefficient pi.toNonUnitalStarAlgHom x x =
      Representation.vectorFunctional pi x := by
  ext a
  rfl

end MathlibAnnex.Analysis.CStarAlgebra
