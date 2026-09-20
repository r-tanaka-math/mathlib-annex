import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Domination
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteIsometryAverage
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Uniform error control for isometries with a common escaping range

A finite-corner approximation of a is NOT uniform over arbitrary unitaries.
The two conjugated square terms are controlled instead by the SMALL range
projection ss* (here written s * star s), while star s * s = 1. This avoids
silently interchanging the two projection orientations.
C04 proof-source candidate, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open scoped ComplexOrder CStarAlgebra
namespace MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.CStarBilinear
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

private theorem positive_map_norm_mono (phi : M →L[ℂ] ℂ)
    (hp : ∀ x, 0 ≤ x → 0 ≤ phi x) {x y : M} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖phi x‖ ≤ ‖phi y‖ := by
  have h : phi x ≤ phi y := by
    apply sub_nonneg.mp
    simpa only [map_sub] using hp (y - x) (sub_nonneg.mpr hxy)
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hp x hx) h

/-- Positive functional domination of a conjugated square. -/
theorem positive_conjugate_square_bound (phi : M →L[ℂ] ℂ)
    (hp : ∀ x, 0 ≤ x → 0 ≤ phi x) (s d : M) :
    ‖phi (s * (star d * d) * star s)‖ ≤ ‖d‖ ^ 2 * ‖phi (s * star s)‖ := by
  have hx : 0 ≤ s * (star d * d) * star s :=
    star_right_conjugate_nonneg (star_mul_self_nonneg d) s
  have h := CStarAlgebra.star_right_conjugate_le_norm_smul
    (a := s) (b := star d * d) (IsSelfAdjoint.star_mul_self d)
  have hn : ‖star d * d‖ = ‖d‖ ^ 2 := by
    simpa only [pow_two] using CStarRing.norm_star_mul_self (x := d)
  rw [hn] at h
  have hm := positive_map_norm_mono phi hp hx h
  have he : phi ((‖d‖ ^ 2 : ℝ) • (s * star s)) =
      (‖d‖ ^ 2 : ℝ) • phi (s * star s) :=
    (phi.restrictScalars ℝ).map_smul _ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hm
  exact hm

/-- The first error slot is d*s*, not s*d. -/
theorem gauge_mul_star_sq_le (phi : M →L[ℂ] ℂ)
    (hp : ∀ x, 0 ≤ x → 0 ≤ phi x) (s d : M) (hs : star s * s = 1) :
    strongStarGauge phi (d * star s) ^ 2 ≤
      ‖d‖ ^ 2 * ‖phi (s * star s)‖ + strongStarGauge phi d ^ 2 := by
  have h1 : star (d * star s) * (d * star s) = s * (star d * d) * star s := by
    simp only [star_mul, star_star]; noncomm_ring
  have h2 : (d * star s) * star (d * star s) = d * star d := by
    simp only [star_mul, star_star]
    calc
      _ = d * (star s * s) * star d := by noncomm_ring
      _ = d * star d := by rw [hs, mul_one]
  simp only [strongStarGauge, Real.sq_sqrt (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    h1, h2]
  linarith [positive_conjugate_square_bound phi hp s d, norm_nonneg (phi (star d * d))]

/-- The second error slot is s*d; both source squares are retained. -/
theorem gauge_mul_sq_le (phi : M →L[ℂ] ℂ)
    (hp : ∀ x, 0 ≤ x → 0 ≤ phi x) (s d : M) (hs : star s * s = 1) :
    strongStarGauge phi (s * d) ^ 2 ≤
      strongStarGauge phi d ^ 2 + ‖d‖ ^ 2 * ‖phi (s * star s)‖ := by
  have h1 : star (s * d) * (s * d) = star d * d := by
    simp only [star_mul]
    calc
      _ = star d * (star s * s) * d := by noncomm_ring
      _ = star d * d := by rw [hs, mul_one]
  have h2 : (s * d) * star (s * d) = s * (d * star d) * star s := by
    simp only [star_mul]; noncomm_ring
  have hc := positive_conjugate_square_bound phi hp s (star d)
  simp only [star_star, norm_star] at hc
  simp only [strongStarGauge, Real.sq_sqrt (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    h1, h2]
  linarith [hc, norm_nonneg (phi (d * star d))]

/-- A contractive functional has gauge at most 2 on an isometry or coisometry. -/
theorem gauge_le_two_of_norm_le_one (phi : M →L[ℂ] ℂ) (hphi : ‖phi‖ ≤ 1)
    (s : M) (hs : ‖s‖ ≤ 1) : strongStarGauge phi s ≤ 2 := by
  have hs2 : ‖s‖ * ‖s‖ ≤ 1 := by
    calc
      _ ≤ ‖s‖ * 1 := mul_le_mul_of_nonneg_left hs (norm_nonneg s)
      _ = ‖s‖ := mul_one _
      _ ≤ 1 := hs
  have hstar : ‖star s * s‖ ≤ 1 := by
    calc
      _ ≤ ‖star s‖ * ‖s‖ := norm_mul_le _ _
      _ = ‖s‖ * ‖s‖ := by rw [norm_star]
      _ ≤ 1 := hs2
  have hreverse : ‖s * star s‖ ≤ 1 := by
    calc
      _ ≤ ‖s‖ * ‖star s‖ := norm_mul_le _ _
      _ = ‖s‖ * ‖s‖ := by rw [norm_star]
      _ ≤ 1 := hs2
  have hleft : ‖phi (star s * s)‖ ≤ 1 := calc
    _ ≤ ‖phi‖ * ‖star s * s‖ := phi.le_opNorm _
    _ ≤ 1 * 1 := mul_le_mul hphi hstar (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
  have hright : ‖phi (s * star s)‖ ≤ 1 := calc
    _ ≤ ‖phi‖ * ‖s * star s‖ := phi.le_opNorm _
    _ ≤ 1 * 1 := mul_le_mul hphi hreverse (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1
  have hsquare : strongStarGauge phi s ^ 2 ≤ 2 := by
    rw [strongStarGauge, Real.sq_sqrt (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith
  nlinarith [strongStarGauge_nonneg phi s]

/-- Quantitative two-slot error.  The four small-square hypotheses are
actual inequalities for the SAME s and d.  They are not independently
chosen vectors and not an assertion of existence of the escaping range. -/
theorem central_error_of_small_gauges [Nontrivial M]
    (B : ContinuousBilinearForm M) (phi psi : M →L[ℂ] ℂ) (C delta : ℝ)
    (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hB : IsStrongStarDominated B phi psi C)
    (hphi : ‖phi‖ ≤ 1) (hpsi : ‖psi‖ ≤ 1)
    (s : Isometry M) (d : M)
    (hleft : strongStarGauge phi (d * star s.val) ≤ 2 * delta)
    (hright : strongStarGauge psi (s.val * d) ≤ 2 * delta) :
    ‖B (d * star s.val) s.val - B (star s.val) (s.val * d)‖ ≤ 8 * C * delta := by
  have hsp := gauge_le_two_of_norm_le_one phi hphi (star s.val)
    (by simp only [norm_star, norm_isometry, le_refl])
  have hsq := gauge_le_two_of_norm_le_one psi hpsi s.val
    (le_of_eq (norm_isometry M s))
  have hL := hB (d * star s.val) s.val
  have hR := hB (star s.val) (s.val * d)
  have hL' : ‖B (d * star s.val) s.val‖ ≤ 4 * C * delta := calc
    _ ≤ C * strongStarGauge phi (d * star s.val) * strongStarGauge psi s.val := hL
    _ ≤ C * (2 * delta) * 2 := mul_le_mul
      (mul_le_mul_of_nonneg_left hleft hC) hsq (strongStarGauge_nonneg _ _)
      (mul_nonneg hC (mul_nonneg (by norm_num) hdelta))
    _ = 4 * C * delta := by ring
  have hR' : ‖B (star s.val) (s.val * d)‖ ≤ 4 * C * delta := calc
    _ ≤ C * strongStarGauge phi (star s.val) * strongStarGauge psi (s.val * d) := hR
    _ ≤ C * 2 * (2 * delta) := mul_le_mul
      (mul_le_mul_of_nonneg_left hsp hC) hright (strongStarGauge_nonneg _ _)
      (mul_nonneg hC (by norm_num))
    _ = 4 * C * delta := by ring
  exact (norm_sub_le _ _).trans (by linarith)

/-- The small source-square and range-mass budgets imply the required
uniform error gauges. The two projection terms are NOT dropped. -/
theorem central_error_of_escape [Nontrivial M]
    (B : ContinuousBilinearForm M) (phi psi : M →L[ℂ] ℂ) (C delta : ℝ)
    (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hB : IsStrongStarDominated B phi psi C)
    (hphi : ‖phi‖ ≤ 1) (hpsi : ‖psi‖ ≤ 1)
    (hp : ∀ x, 0 ≤ x → 0 ≤ phi x) (hq : ∀ x, 0 ≤ x → 0 ≤ psi x)
    (s : Isometry M) (d : M)
    (hdp : strongStarGauge phi d ≤ delta) (hdq : strongStarGauge psi d ≤ delta)
    (hrp : ‖d‖ ^ 2 * ‖phi (s.val * star s.val)‖ ≤ delta ^ 2)
    (hrq : ‖d‖ ^ 2 * ‖psi (s.val * star s.val)‖ ≤ delta ^ 2) :
    ‖B (d * star s.val) s.val - B (star s.val) (s.val * d)‖ ≤ 8 * C * delta := by
  have hp2 : strongStarGauge phi d ^ 2 ≤ delta ^ 2 :=
    (sq_le_sq₀ (strongStarGauge_nonneg _ _) hdelta).mpr hdp
  have hq2 : strongStarGauge psi d ^ 2 ≤ delta ^ 2 :=
    (sq_le_sq₀ (strongStarGauge_nonneg _ _) hdelta).mpr hdq
  have hl := gauge_mul_star_sq_le phi hp s.val d s.property
  have hr := gauge_mul_sq_le psi hq s.val d s.property
  have hleft : strongStarGauge phi (d * star s.val) ≤ 2 * delta := by
    nlinarith [strongStarGauge_nonneg phi (d * star s.val), sq_nonneg delta]
  have hright : strongStarGauge psi (s.val * d) ≤ 2 * delta := by
    nlinarith [strongStarGauge_nonneg psi (s.val * d), sq_nonneg delta]
  exact central_error_of_small_gauges B phi psi C delta hC hdelta hB
    hphi hpsi s d hleft hright

end MathlibAnnex.CStarAlgebra.TensorAveraging
