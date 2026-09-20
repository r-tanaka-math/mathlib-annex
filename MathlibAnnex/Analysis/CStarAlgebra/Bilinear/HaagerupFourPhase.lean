import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.RowColumnSeparation

/-!
# Four-phase moment identities for the Haagerup analytic step

This file fixes a finite four-root model and records its exact characters.
It does NOT replace circle integration for every polynomial of total degree
at most four: the fourth character has average one here, whereas its circle
average is zero.  Replacement requires checking each variable's signed
exponent in the actual mixed monomials.  In particular, the identities below
alone do not prove any noncommutative fourth-moment estimate.  The A RET1
analytic route uses real Rademacher signs for its planned averaging step,
not an unrestricted four-root substitution.
-/

set_option autoImplicit false

open Finset

namespace MathlibAnnex.CStarBilinear

noncomputable section

/-- The uniform fourth roots of unity, used as a finite Steinhaus variable. -/
def haagerupPhase : Fin 4 → ℂ :=
  ![(1 : ℂ), Complex.I, -1, -Complex.I]

@[simp]
theorem norm_haagerupPhase (k : Fin 4) : ‖haagerupPhase k‖ = 1 := by
  fin_cases k <;> simp [haagerupPhase]

@[simp]
theorem star_mul_haagerupPhase (k : Fin 4) :
    star (haagerupPhase k) * haagerupPhase k = 1 := by
  fin_cases k <;> simp [haagerupPhase, Complex.I_mul_I]

@[simp]
theorem haagerupPhase_mul_star (k : Fin 4) :
    haagerupPhase k * star (haagerupPhase k) = 1 := by
  fin_cases k <;> simp [haagerupPhase, Complex.I_mul_I]

/-- First-character orthogonality for the uniform four-phase model. -/
theorem sum_haagerupPhase :
    ∑ k : Fin 4, haagerupPhase k = 0 := by
  simp [haagerupPhase, Fin.sum_univ_four]

/-- Second-character orthogonality. -/
theorem sum_haagerupPhase_sq :
    ∑ k : Fin 4, haagerupPhase k ^ 2 = 0 := by
  simp [haagerupPhase, Fin.sum_univ_four, Complex.I_mul_I]

/-- Third-character orthogonality. -/
theorem sum_haagerupPhase_cube :
    ∑ k : Fin 4, haagerupPhase k ^ 3 = 0 := by
  have h3 : (-Complex.I) ^ 3 = Complex.I := by
    calc
      _ = -(Complex.I ^ 3) := by ring
      _ = Complex.I := by rw [Complex.I_pow_three]; ring
  simp [haagerupPhase, Fin.sum_univ_four, Complex.I_pow_three, h3]
  norm_num

/-- The fourth character is constant one. -/
theorem sum_haagerupPhase_fourth :
    ∑ k : Fin 4, haagerupPhase k ^ 4 = 4 := by
  have h4 : (-Complex.I) ^ 4 = (1 : ℂ) := by
    calc
      _ = Complex.I ^ 4 := by ring
      _ = 1 := Complex.I_pow_four
  simp [haagerupPhase, Fin.sum_univ_four, Complex.I_pow_four, h4]
  norm_num

/-- Exact normalized first moment, with the division made explicit for later
finite-product averaging. -/
theorem average_haagerupPhase :
    (1 / 4 : ℂ) * ∑ k : Fin 4, haagerupPhase k = 0 := by
  rw [sum_haagerupPhase]
  simp

/-- Exact normalized covariance of the finite Steinhaus variable. -/
theorem average_haagerupPhase_covariance :
    (1 / 4 : ℂ) *
        ∑ k : Fin 4, star (haagerupPhase k) * haagerupPhase k = 1 := by
  simp_rw [star_mul_haagerupPhase]
  norm_num [Fin.sum_univ_four]

end

end MathlibAnnex.CStarBilinear
