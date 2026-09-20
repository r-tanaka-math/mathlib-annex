import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.NormalizedFamilies
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.RowColumnSeparation

/-!
# All complex input families and all four square budgets

The real and imaginary algebra parts are constructed explicitly.  Their
squares add to (x*x+xx*)/2, and both orientations are retained after taking
finite sums and norms.  In particular the C01 input maps need NOT preserve
selfadjointness. SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped ComplexOrder
namespace MathlibAnnex.CStarBilinear.Analytic

universe u v w
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The selfadjoint real part in the original algebra. -/
def selfAdjointReal (x : A) : A := (1 / 2 : ℂ) • (x + star x)

/-- The selfadjoint imaginary part; the complex scalar is applied explicitly. -/
def selfAdjointImag (x : A) : A := (-Complex.I) • ((1 / 2 : ℂ) • (x - star x))

theorem selfAdjointReal_sa (x : A) : IsSelfAdjoint (selfAdjointReal x) := by
  change star (selfAdjointReal x) = selfAdjointReal x
  simp [selfAdjointReal, star_smul, star_add, Complex.star_def, add_comm]

theorem selfAdjointImag_sa (x : A) : IsSelfAdjoint (selfAdjointImag x) := by
  change star (selfAdjointImag x) = selfAdjointImag x
  simp only [selfAdjointImag, star_smul, star_sub, star_star]
  norm_num [Complex.star_def] <;> module

theorem selfAdjoint_parts_recover (x : A) :
    selfAdjointReal x + Complex.I • selfAdjointImag x = x := by
  simp only [selfAdjointReal, selfAdjointImag, smul_smul, mul_neg,
    Complex.I_mul_I, neg_neg, one_mul]
  match_scalars <;> (ring_nf; norm_num [Complex.I_sq])

/-- Ordered noncommutative identity; no x*(star x) = (star x)*x assumption. -/
theorem selfAdjoint_parts_squares (x : A) :
    selfAdjointReal x ^ 2 + selfAdjointImag x ^ 2 =
      (1 / 2 : ℝ) • (star x * x + x * star x) := by
  have hi : selfAdjointImag x ^ 2 = -(((1 / 2 : ℂ) • (x - star x)) ^ 2) := by
    simp [selfAdjointImag, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_sq] <;> match_scalars <;> (ring_nf; norm_num [Complex.I_sq])
  rw [hi, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [selfAdjointReal, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
    add_mul, mul_add, sub_mul, mul_sub]
  norm_num <;> module

variable {ι : Type w} [Fintype ι]

/-- Exact finite-sum identity before any norm estimate is used. -/
theorem squareBudget_parts (x : ι → A) :
    squareBudget (fun i ↦ selfAdjointReal (x i)) +
      squareBudget (fun i ↦ selfAdjointImag (x i)) =
      (1 / 2 : ℝ) • (starMulSum x + mulStarSum x) := by
  calc
    _ = ∑ i, (selfAdjointReal (x i) ^ 2 + selfAdjointImag (x i) ^ 2) := by
      rw [Finset.sum_add_distrib]; rfl
    _ = ∑ i, (1 / 2 : ℝ) • (star (x i) * x i + x i * star (x i)) := by
      apply Finset.sum_congr rfl; intro i _; exact selfAdjoint_parts_squares (x i)
    _ = _ := by
      simp [starMulSum, mulStarSum, Finset.smul_sum, smul_add, Finset.sum_add_distrib]

/-- The two selfadjoint budgets are paid for by BOTH star-square orientations. -/
theorem norm_squareBudget_parts_le (x : ι → A) :
    ‖squareBudget (fun i ↦ selfAdjointReal (x i))‖ +
      ‖squareBudget (fun i ↦ selfAdjointImag (x i))‖ ≤
       ‖starMulSum x‖ + ‖mulStarSum x‖ := by
  classical
  let P := squareBudget (fun i ↦ selfAdjointReal (x i))
  let Q := squareBudget (fun i ↦ selfAdjointImag (x i))
  have hP : 0 ≤ P := squareBudget_nonneg _ fun i ↦ selfAdjointReal_sa (x i)
  have hQ : 0 ≤ Q := squareBudget_nonneg _ fun i ↦ selfAdjointImag_sa (x i)
  have hPQ : P ≤ P + Q := by simpa using add_le_add_left hQ P
  have hQP : Q ≤ P + Q := by simpa using add_le_add_right hP Q
  have hNP := CStarAlgebra.norm_le_norm_of_nonneg_of_le hP hPQ
  have hNQ := CStarAlgebra.norm_le_norm_of_nonneg_of_le hQ hQP
  have he : ‖P + Q‖ = (1 / 2 : ℝ) * ‖starMulSum x + mulStarSum x‖ := by
    change ‖squareBudget (fun i ↦ selfAdjointReal (x i)) +
      squareBudget (fun i ↦ selfAdjointImag (x i))‖ = _
    rw [squareBudget_parts, norm_smul]
    norm_num
  have hadd := norm_add_le (starMulSum x) (mulStarSum x)
  change ‖P‖ + ‖Q‖ ≤ _
  linarith

variable {D : Type v} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Exact complex bilinear expansion on the constructed parts. -/
theorem bilinear_parts (V : A →L[ℂ] D →L[ℂ] ℂ) (x : A) (y : D) :
    V x y = V (selfAdjointReal x) (selfAdjointReal y) +
      Complex.I * V (selfAdjointImag x) (selfAdjointReal y) +
      Complex.I * V (selfAdjointReal x) (selfAdjointImag y) -
      V (selfAdjointImag x) (selfAdjointImag y) := by
  calc
    V x y = V (selfAdjointReal x + Complex.I • selfAdjointImag x)
        (selfAdjointReal y + Complex.I • selfAdjointImag y) := by
      rw [selfAdjoint_parts_recover, selfAdjoint_parts_recover]
    _ = _ := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add]
      simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
      ring

/-- Norm bound for the four terms of a complex-bilinear part decomposition. -/
theorem complex_four_term_norm (z₁ z₂ z₃ z₄ : ℂ) :
    ‖z₁ + Complex.I * z₂ + Complex.I * z₃ - z₄‖ ≤
      ‖z₁‖ + ‖z₂‖ + ‖z₃‖ + ‖z₄‖ := by
  calc
    _ ≤ ‖z₁ + Complex.I * z₂ + Complex.I * z₃‖ + ‖z₄‖ := norm_sub_le _ _
    _ ≤ (‖z₁ + Complex.I * z₂‖ + ‖Complex.I * z₃‖) + ‖z₄‖ := by
      have h := norm_add_le (z₁ + Complex.I * z₂) (Complex.I * z₃)
      linarith
    _ ≤ ((‖z₁‖ + ‖Complex.I * z₂‖) + ‖Complex.I * z₃‖) + ‖z₄‖ := by
      have h := norm_add_le z₁ (Complex.I * z₂)
      linarith
    _ = _ := by simp [norm_mul]

/-- The normalized analytic estimate for arbitrary complex finite families.
The constant 73 is independent of ι, including its universe and cardinality. -/
theorem normalized_complex_family_le [Nontrivial A] [Nontrivial D]
    (V : A →L[ℂ] D →L[ℂ] ℂ) (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (x : ι → A) (y : ι → D) :
    ‖∑ i, V (x i) (y i)‖ ≤
      73 * (‖starMulSum x‖ + ‖mulStarSum x‖ + ‖starMulSum y‖ + ‖mulStarSum y‖) := by
  classical
  let a := fun i ↦ selfAdjointReal (x i)
  let b := fun i ↦ selfAdjointImag (x i)
  let c := fun i ↦ selfAdjointReal (y i)
  let d := fun i ↦ selfAdjointImag (y i)
  have ha : ∀ i, IsSelfAdjoint (a i) := fun i ↦ selfAdjointReal_sa _
  have hb : ∀ i, IsSelfAdjoint (b i) := fun i ↦ selfAdjointImag_sa _
  have hc : ∀ i, IsSelfAdjoint (c i) := fun i ↦ selfAdjointReal_sa _
  have hd : ∀ i, IsSelfAdjoint (d i) := fun i ↦ selfAdjointImag_sa _
  have h₁ := normalized_selfAdjoint_family_le V hV h1 a ha c hc
  have h₂ := normalized_selfAdjoint_family_le V hV h1 b hb c hc
  have h₃ := normalized_selfAdjoint_family_le V hV h1 a ha d hd
  have h₄ := normalized_selfAdjoint_family_le V hV h1 b hb d hd
  have he : (∑ i, V (x i) (y i)) = (∑ i, V (a i) (c i)) +
      Complex.I * (∑ i, V (b i) (c i)) +
      Complex.I * (∑ i, V (a i) (d i)) - (∑ i, V (b i) (d i)) := by
    calc
      _ = ∑ i, (V (a i) (c i) + Complex.I * V (b i) (c i) +
          Complex.I * V (a i) (d i) - V (b i) (d i)) := by
        apply Finset.sum_congr rfl; intro i _; exact bilinear_parts V _ _
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he]
  have hn := complex_four_term_norm (∑ i, V (a i) (c i)) (∑ i, V (b i) (c i))
    (∑ i, V (a i) (d i)) (∑ i, V (b i) (d i))
  have hx : ‖squareBudget a‖ + ‖squareBudget b‖ ≤ ‖starMulSum x‖ + ‖mulStarSum x‖ :=
    norm_squareBudget_parts_le x
  have hy : ‖squareBudget c‖ + ‖squareBudget d‖ ≤ ‖starMulSum y‖ + ‖mulStarSum y‖ :=
    norm_squareBudget_parts_le y
  linarith

end MathlibAnnex.CStarBilinear.Analytic
