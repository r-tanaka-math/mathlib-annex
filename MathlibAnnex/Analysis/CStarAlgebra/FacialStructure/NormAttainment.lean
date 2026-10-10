/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PositiveContraction
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitaryTransitivity
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.MatrixCoefficient
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Norm attainment in genuinely nonunital irreducible representations

A positive contraction with one represented unit fixed vector is first obtained
inside `A` by nonunital functional calculus. Unitary transitivity in the canonical
unitization transports this fixed vector to a prescribed unit vector. Conjugation
preserves `A`: the scalar coordinate of the conjugated element is zero.

Multiplying such a positive contraction by a unitary of the unitization gives a
norm-one element of `A` carrying any prescribed unit vector to any other. This
proves exact matrix-coefficient norm attainment and the sharp norm formula.
No rank-one operator is asserted to belong to the represented image, and no unit
is assumed in `A`. Zero vectors are retained in the coefficient statements.
-/

set_option autoImplicit false

noncomputable section

open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra
namespace NonUnitalCStarRepresentation

variable {A H : Type*} [NonUnitalCStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_eq_one_of_norm_le_one_of_apply_eq
    (pi : NonUnitalCStarRepresentation A H) (a : A)
    {xi eta : H} (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (ha : ‖a‖ ≤ 1) (heq : pi a xi = eta) : ‖a‖ = 1 := by
  apply le_antisymm ha
  calc
    1 = ‖pi a xi‖ := by rw [heq, heta]
    _ ≤ ‖pi a‖ * ‖xi‖ := (pi a).le_opNorm xi
    _ ≤ ‖a‖ * ‖xi‖ :=
      mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le pi a) (norm_nonneg xi)
    _ = ‖a‖ := by rw [hxi, mul_one]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- A prescribed unit vector is fixed by a represented positive norm-one element
of the original, possibly nonunital, algebra. -/
theorem exists_nonneg_norm_eq_one_and_apply_eq_self_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (xi : H) (hxi : ‖xi‖ = 1) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ = 1 ∧ pi a xi = xi := by
  obtain ⟨c, hc, hcnorm, eta, heta, hfix⟩ :=
    exists_nonneg_norm_le_one_and_exists_norm_eq_one_apply_eq_self pi hpi.1
  obtain ⟨u, hu⟩ := Representation.exists_unitary_apply_eq_of_isIrreducible
    pi.unitization (isIrreducible_unitization pi hpi) xi eta hxi heta
  let z : Unitization ℂ A :=
    star (u : Unitization ℂ A) * (c : Unitization ℂ A) * (u : Unitization ℂ A)
  let a : A := z.snd
  have hzfst : z.fst = 0 := by simp [z]
  have hz : z = (a : Unitization ℂ A) := by
    apply Unitization.ext
    · simpa [a] using hzfst
    · rfl
  have ha : 0 ≤ a := by
    apply Unitization.inr_nonneg_iff.mp
    rw [← hz]
    exact star_left_conjugate_nonneg (Unitization.inr_nonneg_iff.mpr hc) u
  have hanorm : ‖a‖ ≤ 1 := by
    have hinr : ‖(a : Unitization ℂ A)‖ = ‖a‖ := Unitization.norm_inr a
    rw [← hinr, ← hz]
    dsimp only [z]
    simpa only [CStarRing.norm_mul_coe_unitary, ← Unitary.coe_star,
      CStarRing.norm_coe_unitary_mul, Unitization.norm_inr] using hcnorm
  have hact : pi a xi = xi := by
    rw [← unitization_inr_apply pi a xi, ← hz]
    dsimp only [z]
    rw [map_mul, map_mul]
    change pi.unitization (star (u : Unitization ℂ A))
      (pi.unitization (c : Unitization ℂ A) (pi.unitization (u : Unitization ℂ A) xi)) = xi
    rw [hu, unitization_inr_apply, hfix, ← hu]
    have hunit : pi.unitization (star (u : Unitization ℂ A)) *
        pi.unitization (u : Unitization ℂ A) = 1 := by
      rw [← map_mul, Unitary.coe_star_mul_self, map_one]
    change (pi.unitization (star (u : Unitization ℂ A)) *
      pi.unitization (u : Unitization ℂ A)) xi = xi
    rw [hunit]
    rfl
  exact ⟨a, ha, norm_eq_one_of_norm_le_one_of_apply_eq pi a hxi hxi hanorm hact, hact⟩

end Ordered

/-- Exact norm-one interpolation between two unit vectors, with the interpolant
in the original nonunital algebra rather than merely its unitization. -/
theorem exists_norm_eq_one_and_apply_eq_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    ∃ a : A, ‖a‖ = 1 ∧ pi a xi = eta := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨c, -, hcnorm, hfix⟩ :=
    exists_nonneg_norm_eq_one_and_apply_eq_self_of_isIrreducible pi hpi xi hxi
  obtain ⟨u, hu⟩ := Representation.exists_unitary_apply_eq_of_isIrreducible
    pi.unitization (isIrreducible_unitization pi hpi) xi eta hxi heta
  let z : Unitization ℂ A := (u : Unitization ℂ A) * (c : Unitization ℂ A)
  let a : A := z.snd
  have hzfst : z.fst = 0 := by simp [z]
  have hz : z = (a : Unitization ℂ A) := by
    apply Unitization.ext
    · simpa [a] using hzfst
    · rfl
  have hanorm : ‖a‖ = 1 := by
    have hinr : ‖(a : Unitization ℂ A)‖ = ‖a‖ := Unitization.norm_inr a
    rw [← hinr, ← hz]
    simpa only [z, CStarRing.norm_coe_unitary_mul, Unitization.norm_inr] using hcnorm
  refine ⟨a, hanorm, ?_⟩
  rw [← unitization_inr_apply pi a xi, ← hz]
  dsimp only [z]
  rw [map_mul]
  change pi.unitization (u : Unitization ℂ A)
    (pi.unitization (c : Unitization ℂ A) xi) = eta
  rw [unitization_inr_apply, hfix, hu]

/-- A coefficient of two unit vectors takes the value one at a norm-one element
of the original algebra. -/
theorem exists_norm_eq_one_matrixCoefficient_eq_one_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    ∃ a : A, ‖a‖ = 1 ∧ matrixCoefficient pi xi eta a = 1 := by
  obtain ⟨a, ha, heq⟩ := exists_norm_eq_one_and_apply_eq_of_isIrreducible
    pi hpi xi eta hxi heta
  refine ⟨a, ha, ?_⟩
  rw [matrixCoefficient_apply, heq, inner_self_eq_norm_sq_to_K, heta]
  norm_num

/-- Sharp coefficient attainment for arbitrary vectors, including both zero cases.
The attained value is real and nonnegative; a phase correction is not omitted. -/
theorem exists_norm_le_one_matrixCoefficient_eq_norm_mul_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (xi eta : H) :
    ∃ a : A, ‖a‖ ≤ 1 ∧
      matrixCoefficient pi xi eta a = (‖xi‖ : ℂ) * (‖eta‖ : ℂ) := by
  by_cases hxi : xi = 0
  · exact ⟨0, by norm_num, by simp [hxi, matrixCoefficient_apply]⟩
  by_cases heta : eta = 0
  · exact ⟨0, by norm_num, by simp [heta, matrixCoefficient_apply]⟩
  have hxi_pos : 0 < ‖xi‖ := norm_pos_iff.mpr hxi
  have heta_pos : 0 < ‖eta‖ := norm_pos_iff.mpr heta
  have hxiC : (‖xi‖ : ℂ) ≠ 0 := by exact_mod_cast hxi_pos.ne'
  have hetaC : (‖eta‖ : ℂ) ≠ 0 := by exact_mod_cast heta_pos.ne'
  let x : H := (‖xi‖ : ℂ)⁻¹ • xi
  let y : H := (‖eta‖ : ℂ)⁻¹ • eta
  have hx : ‖x‖ = 1 := by
    simp only [x, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hxi_pos, inv_mul_cancel₀ hxi_pos.ne']
  have hy : ‖y‖ = 1 := by
    simp only [y, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos heta_pos, inv_mul_cancel₀ heta_pos.ne']
  obtain ⟨a, ha, haxy⟩ := exists_norm_eq_one_and_apply_eq_of_isIrreducible pi hpi x y hx hy
  have hxrecover : (‖xi‖ : ℂ) • x = xi := by
    simp only [x, smul_smul, mul_inv_cancel₀ hxiC, one_smul]
  have haxi : pi a xi = (‖xi‖ : ℂ) • y := by
    calc
      pi a xi = pi a ((‖xi‖ : ℂ) • x) := congrArg (pi a) hxrecover.symm
      _ = (‖xi‖ : ℂ) • pi a x := map_smul (pi a) _ _
      _ = (‖xi‖ : ℂ) • y := by rw [haxy]
  refine ⟨a, ha.le, ?_⟩
  rw [matrixCoefficient_apply, haxi, inner_smul_right]
  dsimp only [y]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  field_simp [hetaC] <;> norm_cast <;> ring

/-- In any nonzero irreducible representation the norm of a matrix coefficient is
the product of the vector norms, also for a genuinely nonunital algebra. -/
theorem norm_matrixCoefficient_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) (xi eta : H) :
    ‖matrixCoefficient pi xi eta‖ = ‖xi‖ * ‖eta‖ := by
  apply le_antisymm (norm_matrixCoefficient_le pi xi eta)
  obtain ⟨a, ha, hvalue⟩ :=
    exists_norm_le_one_matrixCoefficient_eq_norm_mul_of_isIrreducible pi hpi xi eta
  have hnorm : ‖matrixCoefficient pi xi eta a‖ = ‖xi‖ * ‖eta‖ := by
    rw [hvalue, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg xi),
      abs_of_nonneg (norm_nonneg eta)]
  calc
    ‖xi‖ * ‖eta‖ = ‖matrixCoefficient pi xi eta a‖ := hnorm.symm
    _ ≤ ‖matrixCoefficient pi xi eta‖ * ‖a‖ := (matrixCoefficient pi xi eta).le_opNorm a
    _ ≤ ‖matrixCoefficient pi xi eta‖ * 1 :=
      mul_le_mul_of_nonneg_left ha (norm_nonneg _)
    _ = ‖matrixCoefficient pi xi eta‖ := mul_one _

/-- Every coefficient in a nonzero irreducible representation attains its norm
on the closed unit ball, with exactly the nonnegative real norm as its value. -/
theorem exists_norm_le_one_matrixCoefficient_eq_norm_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) (xi eta : H) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ matrixCoefficient pi xi eta a = (‖matrixCoefficient pi xi eta‖ : ℂ) := by
  obtain ⟨a, ha, hvalue⟩ :=
    exists_norm_le_one_matrixCoefficient_eq_norm_mul_of_isIrreducible pi hpi xi eta
  refine ⟨a, ha, ?_⟩
  rw [norm_matrixCoefficient_of_isIrreducible pi hpi]
  simpa only [Complex.ofReal_mul] using hvalue

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
