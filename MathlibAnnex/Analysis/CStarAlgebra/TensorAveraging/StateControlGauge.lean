import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RowTestConvergence
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.RowColumnSeparation

/-!
# Exact adapter from the lane-A estimate to all tensor tests

The four selected states are averaged in pairs. Their sum controls both
positive squares, so a factor 2 converts the existing two-sided estimate
into the symmetric two-state gauge consumed by the controller's normal
extension proof. No new analytic inequality is proved or assumed silently:
the exact HasFiniteRowColumnEstimate supplier remains the one lane-A input.

The zero-algebra branch uses the zero tensor and never asks for a normalized
state. The all-test conclusion is row closure of a diagonal bidual point,
not existence or centrality of an invariant mean or of a KOS Omega.
C02 proof-source candidate; unbuilt.
-/
set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarBilinear
open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.ProjectiveTensorProduct MathlibAnnex.FiniteApproximation

universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type v} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

private theorem norm_complex_nonneg_eq_re {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  have h := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hz)
  simpa using h.symm

/-- The actual normalized positive average of two source states. -/
def averageWeakStates (p q : WeakDual ℂ A)
    (hp : p ∈ weakStateSpace A) (hq : q ∈ weakStateSpace A) : StateIndex A := by
  refine ⟨(1 / 2 : ℂ) • (p.toStrongDual + q.toStrongDual), ?_, ?_⟩
  · intro a ha
    change 0 ≤ (1 / 2 : ℂ) * (p a + q a)
    exact mul_nonneg (by norm_num [Complex.nonneg_iff])
      (add_nonneg (hp.1 a ha) (hq.1 a ha))
  · change (1 / 2 : ℂ) * (p 1 + q 1) = 1
    rw [hp.2, hq.2]
    norm_num

@[simp] theorem averageWeakStates_apply (p q : WeakDual ℂ A)
    (hp : p ∈ weakStateSpace A) (hq : q ∈ weakStateSpace A) (a : A) :
    (averageWeakStates p q hp hq).val a = (1 / 2 : ℂ) * (p a + q a) := rfl

/-- Both missing cross-squares are nonnegative; this is why the symmetric
normal gauge may replace the selected asymmetric pair of states. -/
theorem pair_square_le_average_gauge (p q : WeakDual ℂ A)
    (hp : p ∈ weakStateSpace A) (hq : q ∈ weakStateSpace A) (a : A) :
    (p (star a * a)).re + (q (a * star a)).re ≤
      2 * strongStarGauge (averageWeakStates p q hp hq).val a ^ 2 := by
  let phi := averageWeakStates p q hp hq
  have hl : 0 ≤ star a * a := star_mul_self_nonneg a
  have hr : 0 ≤ a * star a := mul_star_self_nonneg a
  have hpR : 0 ≤ (p (a * star a)).re := (RCLike.nonneg_iff.mp (hp.1 _ hr)).1
  have hqL : 0 ≤ (q (star a * a)).re := (RCLike.nonneg_iff.mp (hq.1 _ hl)).1
  have hs : strongStarGauge phi.val a ^ 2 =
      ((p (star a * a)).re + (q (star a * a)).re +
       (p (a * star a)).re + (q (a * star a)).re) / 2 := by
    rw [strongStarGauge, Real.sq_sqrt (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [norm_complex_nonneg_eq_re (phi.property.1 _ hl),
      norm_complex_nonneg_eq_re (phi.property.1 _ hr)]
    simp only [phi, averageWeakStates_apply, Complex.mul_re, Complex.add_re]
    norm_num <;> ring
  change _ ≤ 2 * strongStarGauge phi.val a ^ 2
  rw [hs]
  linarith

/-- An actual row-column estimate gives source states in exactly the form
consumed by NormalStateDomination, with a fixed coarse constant. -/
theorem exists_stateGauge_domination_of_rowColumn
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : HasFiniteRowColumnEstimate B C) :
    ∃ (phi : StateIndex A) (psi : StateIndex D),
      IsStrongStarDominated B phi.val psi.val (2 * C) := by
  obtain ⟨z, hz, hsq⟩ := exists_global_stateControl B C
    (finite_stateControl_of_rowColumn B C hC hrow)
  let phi := averageWeakStates z.1.1 z.1.2 hz.1.1 hz.1.2
  let psi := averageWeakStates z.2.1 z.2.2 hz.2.1 hz.2.2
  refine ⟨phi, psi, fun x y => ?_⟩
  have hl : leftSquare z x ≤ 2 * strongStarGauge phi.val x ^ 2 :=
    pair_square_le_average_gauge z.1.1 z.1.2 hz.1.1 hz.1.2 x
  have hr : rightSquare z y ≤ 2 * strongStarGauge psi.val y ^ 2 :=
    pair_square_le_average_gauge z.2.1 z.2.2 hz.2.1 hz.2.2 y
  have hp : ‖B x y‖ ^ 2 ≤
      ((2 * C) * strongStarGauge phi.val x * strongStarGauge psi.val y) ^ 2 := by
    calc
      ‖B x y‖ ^ 2 ≤ C ^ 2 * leftSquare z x * rightSquare z y := hsq x y
      _ ≤ C ^ 2 * (2 * strongStarGauge phi.val x ^ 2) * rightSquare z y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (sq_nonneg C))
          (rightSquare_nonneg hz y)
      _ ≤ C ^ 2 * (2 * strongStarGauge phi.val x ^ 2) *
          (2 * strongStarGauge psi.val y ^ 2) :=
        mul_le_mul_of_nonneg_left hr
          (mul_nonneg (sq_nonneg C) (mul_nonneg (by norm_num) (sq_nonneg _)))
      _ = ((2 * C) * strongStarGauge phi.val x * strongStarGauge psi.val y) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg (B x y))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC)
      (strongStarGauge_nonneg _ _)) (strongStarGauge_nonneg _ _))).mp hp

@[simp] theorem diagonalTensorPoint_zero :
    diagonalTensorPoint (0 : StrongDual ℂ (StrongDual ℂ A)) = 0 := by
  ext f
  simp only [diagonalTensorPoint_apply, MathlibAnnex.BidualBilinear.firstArens_apply]
  change bidualStar 0 _ = 0
  simp only [bidualStar_apply, ContinuousLinearMap.zero_apply, star_zero]

/-- Total all-test adapter from the precise state-free lane-A supplier.
The output is one actual tensor-dual bidual point with proved row-closure. -/
theorem diagonalTensorPoint_rowClosure_of_estimates
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : ‖F‖ ≤ 1)
    (hest : ∀ B : A →L[ℂ] A →L[ℂ] ℂ, ∃ C : ℝ,
      0 ≤ C ∧ HasFiniteRowColumnEstimate B C) :
    InWeakStarClosure (diagonalTensorPoint F) (rowConvexSet A) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI : Subsingleton A := hA
    have hF0 : F = 0 := by
      ext f
      have hf : f = 0 := by
        ext a
        rw [Subsingleton.elim a 0]
        simp
      simp [hf]
    rw [hF0, diagonalTensorPoint_zero]
    have h0 : (0 : Tensor A) ∈ rowGenerators A := by
      exact ⟨0, by simp, by simp⟩
    simpa only [rowConvexSet, map_zero] using (inWeakStarClosure_of_mem (𝕜 := ℂ) (X := Tensor A)
      ((subset_convexHull ℝ (rowGenerators A)) h0))
  · letI : Nontrivial A := hA
    apply diagonalTensorPoint_mem_rowClosure F hF
    intro f
    obtain ⟨C, hC, hrow⟩ := hest (tensorDualIsometry f)
    obtain ⟨phi, psi, hdom⟩ := exists_stateGauge_domination_of_rowColumn
      (tensorDualIsometry f) C hC hrow
    exact ⟨phi, psi, 2 * C, mul_nonneg (by norm_num) hC, hdom⟩

end MathlibAnnex.RepresentedBidual
