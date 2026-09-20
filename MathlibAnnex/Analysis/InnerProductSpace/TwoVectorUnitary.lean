import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# A small unitary carrying one unit vector to another

The construction is a complex two-dimensional rotation.  It retains the
phase of the inner product, including the collinear pure-phase case, and gives
a uniform operator-norm estimate in the ambient Hilbert space.
-/

set_option autoImplicit false

open scoped ComplexConjugate
open Complex ContinuousLinearMap InnerProductSpace

namespace MathlibAnnex.Analysis.InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def planeUnitaryOperator (x w : H) (a : ℂ) (s : ℝ) :
    H →L[ℂ] H :=
  1 + (a - 1) • rankOne ℂ x x + (s : ℂ) • rankOne ℂ w x -
    (s : ℂ) • rankOne ℂ x w + (conj a - 1) • rankOne ℂ w w

omit [CompleteSpace H] in
private theorem planeUnitaryOperator_apply (x w z : H) (a : ℂ) (s : ℝ) :
    planeUnitaryOperator x w a s z =
      z + ((a - 1) * inner ℂ x z) • x + ((s : ℂ) * inner ℂ x z) • w -
        ((s : ℂ) * inner ℂ w z) • x + ((conj a - 1) * inner ℂ w z) • w := by
  simp [planeUnitaryOperator, mul_smul]

private theorem planeUnitaryOperator_adjoint (x w : H) (a : ℂ) (s : ℝ) :
    star (planeUnitaryOperator x w a s) =
      planeUnitaryOperator x w (conj a) (-s) := by
  simp [planeUnitaryOperator, star_eq_adjoint]
  module

private theorem planeUnitaryOperator_mul_adjoint (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1) :
    planeUnitaryOperator x w (conj a) (-s) * planeUnitaryOperator x w a s = 1 := by
  ext z
  change (planeUnitaryOperator x w (conj a) (-s) *
    planeUnitaryOperator x w a s) z = z
  rw [ContinuousLinearMap.mul_apply]
  rw [planeUnitaryOperator_apply, planeUnitaryOperator_apply]
  have hwx : inner ℂ w x = 0 := by simpa [inner_conj_symm] using congr_arg conj hxw
  simp only [inner_add_right, inner_sub_right, inner_smul_right, hxx, hww, hxw, hwx,
    mul_one, mul_zero, add_zero, sub_zero, zero_mul, one_smul, one_apply,
    map_neg, ofReal_neg, conj_ofReal, conj_conj]
  have ha' : a * conj a + (s : ℂ) * s = 1 := by simpa [mul_comm] using ha
  match_scalars
  · ring
  · linear_combination (inner ℂ x z) * ha'
  · linear_combination (inner ℂ w z) * ha'

private theorem planeUnitaryOperator_adjoint_mul (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1) :
    planeUnitaryOperator x w a s * planeUnitaryOperator x w (conj a) (-s) = 1 := by
  have hunit : conj (conj a) * conj a + ((-s : ℝ) : ℂ) * (-s : ℝ) = 1 := by
    simpa [mul_comm] using ha
  simpa only [conj_conj, neg_neg] using
    planeUnitaryOperator_mul_adjoint x w (conj a) (-s) hxx hww hxw hunit

private noncomputable def planeUnitary (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1) :
    unitary (H →L[ℂ] H) :=
  ⟨planeUnitaryOperator x w a s, by
    rw [Unitary.mem_iff, planeUnitaryOperator_adjoint]
    exact ⟨planeUnitaryOperator_mul_adjoint x w a s hxx hww hxw ha,
      planeUnitaryOperator_adjoint_mul x w a s hxx hww hxw ha⟩⟩

private theorem planeUnitary_apply_left (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1) :
    (planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) x =
      a • x + (s : ℂ) • w := by
  rw [show (planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) =
    planeUnitaryOperator x w a s by rfl, planeUnitaryOperator_apply]
  have hwx : inner ℂ w x = 0 := by simpa [inner_conj_symm] using congr_arg conj hxw
  simp only [hxx, hwx, mul_one, mul_zero, smul_zero, sub_zero, zero_smul]
  module

private theorem star_planeUnitaryOperator_sub_one_mul (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1) :
    star (planeUnitaryOperator x w a s - 1) *
        (planeUnitaryOperator x w a s - 1) =
      (2 - a - conj a) •
        (rankOne ℂ x x + rankOne ℂ w w) := by
  rw [star_sub, star_one, planeUnitaryOperator_adjoint]
  calc
    (planeUnitaryOperator x w (conj a) (-s) - 1) *
        (planeUnitaryOperator x w a s - 1) =
      planeUnitaryOperator x w (conj a) (-s) *
          planeUnitaryOperator x w a s -
        planeUnitaryOperator x w (conj a) (-s) -
        planeUnitaryOperator x w a s + 1 := by noncomm_ring
    _ = 1 - planeUnitaryOperator x w (conj a) (-s) -
        planeUnitaryOperator x w a s + 1 := by
      rw [planeUnitaryOperator_mul_adjoint x w a s hxx hww hxw ha]
    _ = (2 - a - conj a) •
        (rankOne ℂ x x + rankOne ℂ w w) := by
      simp only [planeUnitaryOperator, conj_conj, ofReal_neg]
      module

private theorem isStarProjection_rankOne_pair (x w : H)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0) :
    IsStarProjection (rankOne ℂ x x + rankOne ℂ w w) := by
  have hwx : inner ℂ w x = 0 := by
    simpa [inner_conj_symm] using congrArg conj hxw
  constructor
  · rw [isIdempotentElem_iff]
    ext z
    simp only [mul_apply_eq_comp, add_apply, rankOne_apply, inner_add_right,
      inner_smul_right, hxx, hww, hxw, hwx, mul_one, mul_zero, one_smul,
      zero_smul, add_zero, zero_add]
  · rw [isSelfAdjoint_iff]
    simp [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

private theorem norm_rankOne_pair (x w : H)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0) (hx : ‖x‖ = 1) :
    ‖rankOne ℂ x x + rankOne ℂ w w‖ = 1 := by
  let P : H →L[ℂ] H := rankOne ℂ x x + rankOne ℂ w w
  have hP : IsStarProjection P := isStarProjection_rankOne_pair x w hxx hww hxw
  have hwx : inner ℂ w x = 0 := by
    simpa [inner_conj_symm] using congrArg conj hxw
  have hPx : P x = x := by
    simp only [P, add_apply, rankOne_apply, hxx, hwx, one_smul, zero_smul,
      add_zero]
  apply le_antisymm (hP.norm_le P)
  have hop := P.ratio_le_opNorm x
  simpa [hPx, hx] using hop

private theorem norm_planeUnitary_sub_one_eq (x w : H) (a : ℂ) (s d : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1)
    (hx : ‖x‖ = 1) (hd : 0 ≤ d)
    (hc : 2 - a - conj a = ((d ^ 2 : ℝ) : ℂ)) :
    ‖(planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1‖ = d := by
  let P : H →L[ℂ] H := rankOne ℂ x x + rankOne ℂ w w
  have hPnorm : ‖P‖ = 1 := norm_rankOne_pair x w hxx hww hxw hx
  have hprod :
      star ((planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1) *
          ((planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1) =
        ((d ^ 2 : ℝ) : ℂ) • P := by
    change star (planeUnitaryOperator x w a s - 1) *
        (planeUnitaryOperator x w a s - 1) = _
    rw [star_planeUnitaryOperator_sub_one_mul x w a s hxx hww hxw ha, hc]
  have hsq :
      ‖(planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1‖ ^ 2 = d ^ 2 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, hprod, norm_smul, hPnorm,
      mul_one]
    simp [Real.norm_of_nonneg (sq_nonneg d)]
  nlinarith [norm_nonneg
    ((planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1)]

private theorem norm_planeUnitary_sub_one_le (x w : H) (a : ℂ) (s : ℝ)
    (hxx : inner ℂ x x = 1) (hww : inner ℂ w w = 1)
    (hxw : inner ℂ x w = 0)
    (ha : conj a * a + (s : ℂ) * s = 1)
    (hx : ‖x‖ = 1) (hw : ‖w‖ = 1) :
    ‖(planeUnitary x w a s hxx hww hxw ha : H →L[ℂ] H) - 1‖ ≤
      2 * ‖a - 1‖ + 2 * ‖s‖ := by
  change ‖planeUnitaryOperator x w a s - 1‖ ≤ _
  rw [show planeUnitaryOperator x w a s - 1 =
      (a - 1) • rankOne ℂ x x + (s : ℂ) • rankOne ℂ w x -
        (s : ℂ) • rankOne ℂ x w + (conj a - 1) • rankOne ℂ w w by
    simp [planeUnitaryOperator]; abel]
  calc
    _ ≤ ‖(a - 1) • rankOne ℂ x x‖ + ‖(s : ℂ) • rankOne ℂ w x‖ +
        ‖(s : ℂ) • rankOne ℂ x w‖ + ‖(conj a - 1) • rankOne ℂ w w‖ := by
      grw [norm_add_le, norm_sub_le, norm_add_le]
    _ = 2 * ‖a - 1‖ + 2 * ‖s‖ := by
      have hconj : ‖conj a - 1‖ = ‖a - 1‖ := by
        rw [show conj a - 1 = conj (a - 1) by simp]
        exact norm_conj (a - 1)
      simp [norm_smul, norm_rankOne, hx, hw, hconj]
      ring

private noncomputable def phaseUnitaryOperator (x : H) (a : ℂ) : H →L[ℂ] H :=
  1 + (a - 1) • rankOne ℂ x x

omit [CompleteSpace H] in
private theorem phaseUnitaryOperator_apply (x z : H) (a : ℂ) :
    phaseUnitaryOperator x a z = z + ((a - 1) * inner ℂ x z) • x := by
  simp [phaseUnitaryOperator, mul_smul]

private theorem phaseUnitaryOperator_adjoint (x : H) (a : ℂ) :
    star (phaseUnitaryOperator x a) = phaseUnitaryOperator x (conj a) := by
  simp [phaseUnitaryOperator, star_eq_adjoint]

private theorem phaseUnitaryOperator_mul (x : H) (a : ℂ)
    (hxx : inner ℂ x x = 1) (ha : conj a * a = 1) :
    phaseUnitaryOperator x (conj a) * phaseUnitaryOperator x a = 1 := by
  ext z
  change (phaseUnitaryOperator x (conj a) * phaseUnitaryOperator x a) z = z
  rw [ContinuousLinearMap.mul_apply]
  rw [phaseUnitaryOperator_apply, phaseUnitaryOperator_apply]
  simp only [inner_add_right, inner_smul_right, hxx, mul_one]
  match_scalars
  · ring
  · linear_combination (inner ℂ x z) * ha

private noncomputable def phaseUnitary (x : H) (a : ℂ)
    (hxx : inner ℂ x x = 1) (ha : conj a * a = 1) : unitary (H →L[ℂ] H) :=
  ⟨phaseUnitaryOperator x a, by
    rw [Unitary.mem_iff, phaseUnitaryOperator_adjoint]
    refine ⟨phaseUnitaryOperator_mul x a hxx ha, ?_⟩
    have hunit : conj (conj a) * conj a = 1 := by simpa [mul_comm] using ha
    simpa only [conj_conj] using phaseUnitaryOperator_mul x (conj a) hxx hunit⟩

private theorem phaseUnitary_apply (x : H) (a : ℂ)
    (hxx : inner ℂ x x = 1) (ha : conj a * a = 1) :
    (phaseUnitary x a hxx ha : H →L[ℂ] H) x = a • x := by
  change phaseUnitaryOperator x a x = _
  rw [phaseUnitaryOperator_apply, hxx, mul_one]
  module

private theorem norm_phaseUnitary_sub_one_le (x : H) (a : ℂ)
    (hxx : inner ℂ x x = 1) (ha : conj a * a = 1) (hx : ‖x‖ = 1) :
    ‖(phaseUnitary x a hxx ha : H →L[ℂ] H) - 1‖ ≤ ‖a - 1‖ := by
  change ‖phaseUnitaryOperator x a - 1‖ ≤ _
  rw [show phaseUnitaryOperator x a - 1 = (a - 1) • rankOne ℂ x x by
    simp [phaseUnitaryOperator]]
  simp [norm_smul, norm_rankOne, hx]

private theorem norm_phaseUnitary_sub_one_eq (x : H) (a : ℂ)
    (hxx : inner ℂ x x = 1) (ha : conj a * a = 1) (hx : ‖x‖ = 1) :
    ‖(phaseUnitary x a hxx ha : H →L[ℂ] H) - 1‖ = ‖a - 1‖ := by
  change ‖phaseUnitaryOperator x a - 1‖ = _
  rw [show phaseUnitaryOperator x a - 1 = (a - 1) • rankOne ℂ x x by
    simp [phaseUnitaryOperator]]
  simp [norm_smul, norm_rankOne, hx]

/-- Two unit vectors in a complex Hilbert space are carried exactly by an
ambient unitary whose distance from the identity is the distance between the
vectors.  The construction also covers a pure phase change and antipodal
vectors; it does not use a principal logarithm. -/
theorem exists_unitary_apply_eq_and_norm_sub_one_eq (x y : H)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H) x = y ∧ ‖(u : H →L[ℂ] H) - 1‖ = ‖x - y‖ := by
  let a : ℂ := inner ℂ x y
  let beta : H := y - a • x
  let s : ℝ := ‖beta‖
  have hxx : inner ℂ x x = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hyy : inner ℂ y y = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]
    norm_num
  have hxbeta : inner ℂ x beta = 0 := by
    rw [show beta = y - a • x by rfl, inner_sub_right, inner_smul_right, hxx]
    simp [a]
  have hbeta_sq : ((‖beta‖ : ℂ) ^ 2) = 1 - conj a * a := by
    calc
      ((‖beta‖ : ℂ) ^ 2) = inner ℂ beta beta :=
        (inner_self_eq_norm_sq_to_K beta).symm
      _ = 1 - conj a * a := by
        simp only [beta, inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, hxx, hyy, a]
        rw [inner_conj_symm]
        ring
  have hunit : conj a * a + (s : ℂ) * s = 1 := by
    change conj a * a + (‖beta‖ : ℂ) * ‖beta‖ = 1
    rw [← sq]
    linear_combination hbeta_sq
  have hc : 2 - a - conj a = ((‖x - y‖ ^ 2 : ℝ) : ℂ) := by
    calc
      2 - a - conj a = inner ℂ (x - y) (x - y) := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right, hxx, hyy]
        have hyx : inner ℂ y x = conj a := by
          simpa [a] using inner_conj_symm y x
        rw [hyx]
        simp [a]
        ring
      _ = ((‖x - y‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K (x - y)
      _ = ((‖x - y‖ ^ 2 : ℝ) : ℂ) := by norm_num
  by_cases hbeta : beta = 0
  · have hs : s = 0 := by simp [s, hbeta]
    have hau : conj a * a = 1 := by simpa [hs] using hunit
    let u := phaseUnitary x a hxx hau
    refine ⟨u, ?_, ?_⟩
    · rw [phaseUnitary_apply]
      exact (sub_eq_zero.mp hbeta).symm
    · rw [norm_phaseUnitary_sub_one_eq x a hxx hau hx]
      have hyax : y = a • x := sub_eq_zero.mp hbeta
      calc
        ‖a - 1‖ = ‖1 - a‖ := norm_sub_rev a 1
        _ = ‖(1 - a) • x‖ := by simp [norm_smul, hx]
        _ = ‖x - y‖ := by rw [hyax]; congr 1; module
  · have hspos : 0 < s := by simpa [s, norm_pos_iff] using hbeta
    let w : H := ((s : ℂ)⁻¹) • beta
    have hw : ‖w‖ = 1 := by
      simp only [w, norm_smul, norm_inv, norm_real, Real.norm_eq_abs]
      rw [abs_of_pos hspos]
      exact inv_mul_cancel₀ hspos.ne'
    have hww : inner ℂ w w = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]
      norm_num
    have hxw : inner ℂ x w = 0 := by simp [w, inner_smul_right, hxbeta]
    let u := planeUnitary x w a s hxx hww hxw hunit
    refine ⟨u, ?_, ?_⟩
    · rw [planeUnitary_apply_left]
      have hsne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hspos.ne'
      simp only [w, smul_smul, mul_inv_cancel₀ hsne, one_smul]
      simp [beta]
    · exact norm_planeUnitary_sub_one_eq x w a s ‖x - y‖ hxx hww hxw hunit
        hx (norm_nonneg _) hc

/-- Two unit vectors in a complex Hilbert space are carried exactly by an
ambient unitary whose distance from the identity is at most six times the
distance of the vectors.  The construction includes their complex phase. -/
theorem exists_unitary_apply_eq_and_norm_sub_one_le_six (x y : H)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ u : unitary (H →L[ℂ] H),
      (u : H →L[ℂ] H) x = y ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ 6 * ‖x - y‖ := by
  let a : ℂ := inner ℂ x y
  let beta : H := y - a • x
  let s : ℝ := ‖beta‖
  have hxx : inner ℂ x x = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hyy : inner ℂ y y = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]
    norm_num
  have hxbeta : inner ℂ x beta = 0 := by
    rw [show beta = y - a • x by rfl, inner_sub_right, inner_smul_right, hxx]
    simp [a]
  have hbeta_sq : ((‖beta‖ : ℂ) ^ 2) = 1 - conj a * a := by
    calc
      ((‖beta‖ : ℂ) ^ 2) = inner ℂ beta beta :=
        (inner_self_eq_norm_sq_to_K beta).symm
      _ = 1 - conj a * a := by
        simp only [beta, inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right, hxx, hyy, a]
        rw [inner_conj_symm]
        ring
  have hunit : conj a * a + (s : ℂ) * s = 1 := by
    change conj a * a + (‖beta‖ : ℂ) * ‖beta‖ = 1
    rw [← sq]
    linear_combination hbeta_sq
  have ha_sub : ‖a - 1‖ ≤ ‖x - y‖ := by
    have hid : a - 1 = inner ℂ x (y - x) := by
      rw [inner_sub_right, hxx]
    rw [hid]
    calc
      _ ≤ ‖x‖ * ‖y - x‖ := norm_inner_le_norm x (y - x)
      _ = ‖x - y‖ := by rw [hx, one_mul, norm_sub_rev]
  have hbeta_le : ‖beta‖ ≤ 2 * ‖x - y‖ := by
    have hdecomp : beta = (y - x) + (1 - a) • x := by
      simp [beta]
      module
    rw [hdecomp]
    calc
      _ ≤ ‖y - x‖ + ‖(1 - a) • x‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖1 - a‖ := by
        rw [norm_sub_rev y x, norm_smul, hx, mul_one]
      _ ≤ 2 * ‖x - y‖ := by
        rw [two_mul]
        gcongr
        simpa [norm_sub_rev] using ha_sub
  by_cases hbeta : beta = 0
  · have hs : s = 0 := by simp [s, hbeta]
    have hau : conj a * a = 1 := by simpa [hs] using hunit
    let u := phaseUnitary x a hxx hau
    refine ⟨u, ?_, ?_⟩
    · rw [phaseUnitary_apply]
      exact (sub_eq_zero.mp hbeta).symm
    · calc
        _ ≤ ‖a - 1‖ := norm_phaseUnitary_sub_one_le x a hxx hau hx
        _ ≤ ‖x - y‖ := ha_sub
        _ ≤ 6 * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  · have hspos : 0 < s := by simpa [s, norm_pos_iff] using hbeta
    let w : H := ((s : ℂ)⁻¹) • beta
    have hw : ‖w‖ = 1 := by
      simp only [w, norm_smul, norm_inv, norm_real, Real.norm_eq_abs]
      rw [abs_of_pos hspos]
      exact inv_mul_cancel₀ hspos.ne'
    have hww : inner ℂ w w = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]
      norm_num
    have hxw : inner ℂ x w = 0 := by simp [w, inner_smul_right, hxbeta]
    let u := planeUnitary x w a s hxx hww hxw hunit
    refine ⟨u, ?_, ?_⟩
    · rw [planeUnitary_apply_left]
      have hsne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hspos.ne'
      simp only [w, smul_smul, mul_inv_cancel₀ hsne, one_smul]
      simp [beta]
    · calc
        _ ≤ 2 * ‖a - 1‖ + 2 * ‖s‖ :=
          norm_planeUnitary_sub_one_le x w a s hxx hww hxw hunit hx hw
        _ ≤ 2 * ‖x - y‖ + 2 * ‖s‖ := by gcongr
        _ ≤ 2 * ‖x - y‖ + 2 * (2 * ‖x - y‖) := by
          gcongr
          simpa [s, Real.norm_of_nonneg (norm_nonneg beta)] using hbeta_le
        _ = 6 * ‖x - y‖ := by ring

end MathlibAnnex.Analysis.InnerProductSpace
