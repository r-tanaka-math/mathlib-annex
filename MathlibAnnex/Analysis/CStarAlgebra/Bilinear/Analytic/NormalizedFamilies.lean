import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.RademacherFourthOrder
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.NormalizedRealPart

/-!
# The dimension-free normalized estimate on selfadjoint finite families

The imaginary part uses exact finite covariance, the constant-36 pointwise
bound, the proved noncommutative fourth moment, and a finite variance identity.
The real part is summed directly.  Empty families and zero budgets are included.
The resulting deliberately coarse constant is 73/2. SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped ComplexOrder
namespace MathlibAnnex.CStarBilinear.Analytic
open MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {A : Type u} {D : Type v}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

/-- Finite scalar triangle bound, with its elementary induction supplied. -/
theorem abs_sum_le_of_pointwise {κ : Type*} (s : Finset κ) (f g : κ → ℝ)
    (h : ∀ i, |f i| ≤ g i) : |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (abs_add_le _ _).trans (add_le_add (h i) ih)

/-- The finite mean of the square root of a fourth moment is controlled by
2||P||.  This deliberately rounds sqrt(3) up to 2, without division by ||P||. -/
theorem finiteMean_sqrt_fourthMoment_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i)) :
    finiteMean (fun ε : ι → Bool ↦ Real.sqrt (fourthMoment phi (rademacherSum a ε))) ≤
      2 * ‖squareBudget a‖ := by
  let m : (ι → Bool) → ℝ := fun ε ↦ fourthMoment phi (rademacherSum a ε)
  have hm : ∀ ε, 0 ≤ m ε := fun ε ↦
    fourthMoment_nonneg phi hphi _ (isSelfAdjoint_rademacherSum a ha ε)
  have hs := finiteMean_sq_le (fun ε : ι → Bool ↦ Real.sqrt (m ε))
  have he : finiteMean (fun ε : ι → Bool ↦ Real.sqrt (m ε) ^ 2) = finiteMean m :=
    finiteMean_congr fun ε ↦ Real.sq_sqrt (hm ε)
  rw [he] at hs
  have hfour : finiteMean m ≤ 3 * ‖squareBudget a‖ ^ 2 :=
    finiteMean_fourthMoment_le phi hphi a ha
  have hmean0 : 0 ≤ finiteMean (fun ε : ι → Bool ↦ Real.sqrt (m ε)) :=
    finiteMean_nonneg fun ε ↦ Real.sqrt_nonneg _
  change finiteMean (fun ε : ι → Bool ↦ Real.sqrt (m ε)) ≤ 2 * ‖squareBudget a‖
  nlinarith [norm_nonneg (squareBudget a)]

/-- Finite Holder's inequality in the only form needed here, proved from the
pointwise square (fourthRoot m - fourthRoot n)^2. -/
theorem finiteMean_fourthRoot_product_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m n : Ω → ℝ) (P Q : ℝ)
    (hP : finiteMean (fun ω ↦ Real.sqrt (m ω)) ≤ 2 * P)
    (hQ : finiteMean (fun ω ↦ Real.sqrt (n ω)) ≤ 2 * Q) :
    finiteMean (fun ω ↦ fourthRoot (m ω) * fourthRoot (n ω)) ≤ P + Q := by
  have hp : ∀ ω, fourthRoot (m ω) * fourthRoot (n ω) ≤
      (1 / 2 : ℝ) * (Real.sqrt (m ω) + Real.sqrt (n ω)) := by
    intro ω
    nlinarith [sq_nonneg (fourthRoot (m ω) - fourthRoot (n ω)),
      fourthRoot_sq (m ω), fourthRoot_sq (n ω)]
  have havg := finiteMean_mono hp
  rw [finiteMean_mul, finiteMean_add] at havg
  linarith

/-- The normalized imaginary finite-family estimate is independent of card(ι). -/
theorem normalized_abs_im_sum_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (b : ι → D) (hb : ∀ i, IsSelfAdjoint (b i)) :
    |(∑ i, V (a i) (b i)).im| ≤ 36 * (‖squareBudget a‖ + ‖squareBudget b‖) := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  let m := fun ε : ι → Bool ↦ fourthMoment (leftMarginal V) (rademacherSum a ε)
  let n := fun ε : ι → Bool ↦ fourthMoment (rightMarginal V) (rademacherSum b ε)
  have hprod : finiteMean (fun ε : ι → Bool ↦ fourthRoot (m ε) * fourthRoot (n ε)) ≤
      ‖squareBudget a‖ + ‖squareBudget b‖ :=
    finiteMean_fourthRoot_product_le m n _ _
      (finiteMean_sqrt_fourthMoment_le _ hphi a ha)
      (finiteMean_sqrt_fourthMoment_le _ hpsi b hb)
  have he : finiteMean (fun ε : ι → Bool ↦ V (rademacherSum a ε) (rademacherSum b ε)) =
      ∑ i, V (a i) (b i) := by
    simpa only [rademacherSum, signedSum] using finiteMean_bilinear_signedSum V a b
  calc
    |(∑ i, V (a i) (b i)).im| =
        |finiteMean (fun ε : ι → Bool ↦ (V (rademacherSum a ε) (rademacherSum b ε)).im)| := by
      rw [finiteMean_im, he]
    _ ≤ finiteMean (fun ε : ι → Bool ↦ |(V (rademacherSum a ε) (rademacherSum b ε)).im|) :=
      abs_finiteMean_le _
    _ ≤ finiteMean (fun ε : ι → Bool ↦ 36 * (fourthRoot (m ε) * fourthRoot (n ε))) := by
      apply finiteMean_mono
      intro ε
      have h := normalized_abs_im_quartic_le V hV h1
        _ (isSelfAdjoint_rademacherSum a ha ε) _ (isSelfAdjoint_rademacherSum b hb ε)
      simpa only [m, n, mul_assoc] using h
    _ = 36 * finiteMean (fun ε : ι → Bool ↦ fourthRoot (m ε) * fourthRoot (n ε)) :=
      finiteMean_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)

/-- Summation of the real-part estimate uses the same two marginal states. -/
theorem normalized_abs_re_sum_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (b : ι → D) (hb : ∀ i, IsSelfAdjoint (b i)) :
    |(∑ i, V (a i) (b i)).re| ≤ (‖squareBudget a‖ + ‖squareBudget b‖) / 2 := by
  obtain ⟨hphi, hpsi⟩ := normalized_marginals_are_states V hV h1
  have h := abs_sum_le_of_pointwise Finset.univ (fun i ↦ (V (a i) (b i)).re)
    (fun i ↦ ((leftMarginal V (a i ^ 2)).re + (rightMarginal V (b i ^ 2)).re) / 2)
    (fun i ↦ normalized_abs_re_le_half V hV h1 _ (ha i) _ (hb i))
  have he : (∑ i, ((leftMarginal V (a i ^ 2)).re + (rightMarginal V (b i ^ 2)).re) / 2) =
      ((leftMarginal V (squareBudget a)).re + (rightMarginal V (squareBudget b)).re) / 2 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      ← Complex.re_sum, ← map_sum, squareBudget]
  rw [he, ← Complex.re_sum] at h
  have hP := state_re_le_norm _ hphi _ (squareBudget_nonneg a ha).isSelfAdjoint
  have hQ := state_re_le_norm _ hpsi _ (squareBudget_nonneg b hb).isSelfAdjoint
  linarith

/-- Elementary coordinate estimate, with its scalar norm-square proof supplied. -/
theorem complex_norm_le_coordinates (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have he : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  nlinarith [norm_nonneg z, abs_nonneg z.re, abs_nonneg z.im,
    sq_abs z.re, sq_abs z.im, mul_nonneg (abs_nonneg z.re) (abs_nonneg z.im)]

/-- The first complete normalized finite-family complex-norm estimate, on
selfadjoint inputs only.  No finite-family supplier occurs as a hypothesis. -/
theorem normalized_selfAdjoint_family_le (V : A →L[ℂ] D →L[ℂ] ℂ)
    (hV : ‖V‖ ≤ 1) (h1 : V 1 1 = 1)
    (a : ι → A) (ha : ∀ i, IsSelfAdjoint (a i))
    (b : ι → D) (hb : ∀ i, IsSelfAdjoint (b i)) :
    ‖∑ i, V (a i) (b i)‖ ≤ (73 / 2 : ℝ) * (‖squareBudget a‖ + ‖squareBudget b‖) := by
  have hr := normalized_abs_re_sum_le V hV h1 a ha b hb
  have hi := normalized_abs_im_sum_le V hV h1 a ha b hb
  have hn := complex_norm_le_coordinates (∑ i, V (a i) (b i))
  linarith

end MathlibAnnex.CStarBilinear.Analytic
