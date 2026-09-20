import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MathlibAnnex.Analysis.CStarAlgebra.RowTransport.Local
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Vector residual estimates for exponential paths of self-adjoint operators. -/

set_option autoImplicit false

open NormedSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

theorem exp_apply_sub_self_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (X : H →L[ℂ] H) (v : H) (C : ℝ)
    (hC : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖exp (t • X)‖ ≤ C) :
    ‖exp X v - v‖ ≤ C * ‖X v‖ := by
  have hd (t : ℝ) :
      HasDerivAt (fun s : ℝ => exp (s • X) v) (exp (t • X) (X v)) t := by
    let ev : (H →L[ℂ] H) →L[ℝ] H :=
      (ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ
    have h := ev.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)
    simpa [ev, Function.comp_def, mul_apply_eq_comp] using h
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖exp (t • X) (X v)‖ ≤ C * ‖X v‖ := by
    exact (exp (t • X)).le_opNorm (X v) |>.trans
      (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => exp (t • X) v)
    (f' := fun t : ℝ => exp (t • X) (X v))
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa only [one_smul, zero_smul, exp_zero, ContinuousLinearMap.one_apply] using h

theorem norm_exp_I_selfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (b : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    ‖exp (t • (Complex.I • (b : H →L[ℂ] H)))‖ = 1 := by
  have heq : t • (Complex.I • (b : H →L[ℂ] H)) =
      Complex.I • ((t • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) := by
    change t • (Complex.I • (b : H →L[ℂ] H)) =
      Complex.I • (t • (b : H →L[ℂ] H))
    exact smul_comm t Complex.I (b : H →L[ℂ] H)
  rw [heq, ← selfAdjoint.expUnitary_coe]
  exact CStarRing.norm_coe_unitary _

theorem exp_pi_apply_sub_self_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (b : selfAdjoint (H →L[ℂ] H)) (v : H) :
    ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v - v‖ ≤
      Real.pi * ‖(b : H →L[ℂ] H) v‖ := by
  have hb := exp_apply_sub_self_le
    (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H))
    v 1 (by
      intro t ht
      exact (norm_exp_I_selfAdjoint ((Real.pi : ℝ) • b) t).le)
  have hnorm :
      ‖(Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v‖ =
        Real.pi * ‖(b : H →L[ℂ] H) v‖ := by
    change ‖(Complex.I • ((Real.pi : ℝ) • (b : H →L[ℂ] H))) v‖ = _
    simp [smul_apply, norm_smul, Complex.norm_I, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  simpa only [one_mul, hnorm] using hb

theorem exp_I_pi_one_eq_neg_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] :
    exp ((Complex.I * (Real.pi : ℂ)) • (1 : H →L[ℂ] H)) = -1 := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  let z : ℂ := Complex.I * (Real.pi : ℂ)
  have hz : Complex.exp z = -1 := by
    dsimp [z]
    simpa only [mul_comm] using Complex.exp_pi_mul_I
  calc
    exp (z • (1 : H →L[ℂ] H)) = exp (algebraMap ℂ (H →L[ℂ] H) z) := by
      rw [Algebra.algebraMap_eq_smul_one]
    _ = algebraMap ℂ (H →L[ℂ] H) (exp z) :=
      (NormedSpace.map_exp (algebraMap ℂ (H →L[ℂ] H))
        (continuous_algebraMap ℂ (H →L[ℂ] H)) z).symm
    _ = -1 := by
      rw [← Complex.exp_eq_exp_ℂ, hz]
      simp

theorem exp_I_pi_selfAdjoint_eq_neg_exp_sub_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (b : selfAdjoint (H →L[ℂ] H)) :
    exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) =
      -exp (Complex.I • (((Real.pi : ℝ) • (b - 1) : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) := by
  letI : NormedAlgebra ℚ (H →L[ℂ] H) :=
    NormedAlgebra.restrictScalars ℚ ℂ (H →L[ℂ] H)
  let X : H →L[ℂ] H := Complex.I • (((Real.pi : ℝ) • (b - 1) : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)
  let Y : H →L[ℂ] H := Complex.I • (((Real.pi : ℝ) • (1 : selfAdjoint (H →L[ℂ] H))) : H →L[ℂ] H)
  have heq : Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) = X + Y := by
    dsimp [X, Y]
    change Complex.I • ((Real.pi : ℝ) • (b : H →L[ℂ] H)) =
      Complex.I • ((Real.pi : ℝ) • ((b : H →L[ℂ] H) - 1)) +
        Complex.I • ((Real.pi : ℝ) • (1 : H →L[ℂ] H))
    module
  have hY : Y = (Complex.I * (Real.pi : ℂ)) • (1 : H →L[ℂ] H) := by
    dsimp [Y]
    change Complex.I • ((Real.pi : ℂ) • (1 : H →L[ℂ] H)) = _
    rw [smul_smul]
  have hc : Commute X Y := by
    rw [hY]
    exact (Commute.one_right X).smul_right _
  rw [heq, NormedSpace.exp_add_of_commute hc, hY, exp_I_pi_one_eq_neg_one]
  simp [X]

theorem exp_pi_apply_add_self_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (b : selfAdjoint (H →L[ℂ] H)) (v : H) :
    ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v + v‖ ≤
      Real.pi * ‖(b : H →L[ℂ] H) v - v‖ := by
  have h := exp_pi_apply_sub_self_le (b - 1) v
  have heq := exp_I_pi_selfAdjoint_eq_neg_exp_sub_one b
  have hnorm :
      ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v + v‖ =
        ‖exp (Complex.I • (((Real.pi : ℝ) • (b - 1) : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v - v‖ := by
    rw [heq]
    change ‖-(exp (Complex.I • (((Real.pi : ℝ) • (b - 1) : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v) + v‖ = _
    rw [← norm_neg (exp (Complex.I • (((Real.pi : ℝ) • (b - 1) : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v - v)]
    congr 1
    module
  rw [hnorm]
  have hright :
      ‖(((b - 1 : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) v‖ =
        ‖(b : H →L[ℂ] H) v - v‖ := by
    change ‖((b : H →L[ℂ] H) - 1) v‖ = _
    simp only [sub_apply, one_apply_eq_self]
  rw [hright] at h
  exact h

theorem endpoint_from_sum_difference
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (ξ η : H) :
    ‖T ξ - η‖ ≤
      (‖T (ξ + η) - (ξ + η)‖ + ‖T (ξ - η) + (ξ - η)‖) / 2 := by
  have heq : (2 : ℝ) • (T ξ - η) =
      (T (ξ + η) - (ξ + η)) + (T (ξ - η) + (ξ - η)) := by
    simp only [map_add, map_sub]
    module
  have hn : 2 * ‖T ξ - η‖ =
      ‖(T (ξ + η) - (ξ + η)) + (T (ξ - η) + (ξ - η))‖ := by
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have htri := norm_add_le (T (ξ + η) - (ξ + η)) (T (ξ - η) + (ξ - η))
  nlinarith

theorem exp_pi_endpoint_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (b : selfAdjoint (H →L[ℂ] H)) (ξ η : H) :
    ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) ξ - η‖ ≤
      Real.pi / 2 * (‖(b : H →L[ℂ] H) (ξ + η)‖ +
        ‖(b : H →L[ℂ] H) (ξ - η) - (ξ - η)‖) := by
  let T : H →L[ℂ] H := exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H))
  have hsum := exp_pi_apply_sub_self_le b (ξ + η)
  have hdiff := exp_pi_apply_add_self_le b (ξ - η)
  have h := endpoint_from_sum_difference T ξ η
  dsimp [T] at h
  change ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) ξ - η‖ ≤
      (‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) (ξ + η) - (ξ + η)‖ +
        ‖exp (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H)) (ξ - η) + (ξ - η)‖) / 2 at h
  nlinarith

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

theorem norm_exp_I_selfAdjoint_general (b : selfAdjoint A) (t : ℝ) :
    ‖exp (t • (Complex.I • (b : A)))‖ = 1 := by
  have heq : t • (Complex.I • (b : A)) =
      Complex.I • ((t • b : selfAdjoint A) : A) := by
    change t • (Complex.I • (b : A)) = Complex.I • (t • (b : A))
    exact smul_comm t Complex.I (b : A)
  rw [heq, ← selfAdjoint.expUnitary_coe]
  exact CStarRing.norm_coe_unitary _

theorem hasDerivAt_exp_conjugation (X a : A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • X) * a * exp (s • (-X)))
      (exp (t • X) * (X * a - a * X) * exp (t • (-X))) t := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  have h1 := (hasDerivAt_exp_smul_const X t).mul_const a
  have h2 := hasDerivAt_exp_smul_const' (-X) t
  have h := h1.mul h2
  convert h using 1
  · funext s
    simp only [Pi.mul_apply, mul_assoc]
  · noncomm_ring

theorem norm_exp_conjugation_sub_le
    (b : selfAdjoint A) (a : A) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖exp (t • (Complex.I • (b : A))) * a *
      exp (t • (-(Complex.I • (b : A)))) - a‖ ≤
      t * ‖(Complex.I • (b : A)) * a - a * (Complex.I • (b : A))‖ := by
  let X : A := Complex.I • (b : A)
  let f : ℝ → A := fun s => exp (s • X) * a * exp (s • (-X))
  let f' : ℝ → A := fun s => exp (s • X) * (X * a - a * X) * exp (s • (-X))
  have hd (s : ℝ) : HasDerivAt f (f' s) s := hasDerivAt_exp_conjugation X a s
  have hb (s : ℝ) (_hs : s ∈ Set.Ico (0 : ℝ) 1) :
      ‖f' s‖ ≤ ‖X * a - a * X‖ := by
    have hpos : ‖exp (s • X)‖ = 1 := norm_exp_I_selfAdjoint_general b s
    have hneg : ‖exp (s • (-X))‖ = 1 := by
      simpa only [smul_neg, neg_smul] using
        (norm_exp_I_selfAdjoint_general b (-s))
    dsimp [f']
    calc
      _ ≤ ‖exp (s • X)‖ * ‖X * a - a * X‖ * ‖exp (s • (-X))‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = _ := by rw [hpos, hneg]; ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0:ℝ)) (b := (1:ℝ))
    (f := f) (f' := f')
    (fun s _ => (hd s).hasDerivWithinAt) hb t ht
  have h' : ‖exp (t • X) * a * exp (t • (-X)) - a‖ ≤
      ‖X * a - a * X‖ * t := by
    simpa only [f, zero_smul, exp_zero, one_mul, mul_one, sub_zero] using h
  change ‖exp (t • X) * a * exp (t • (-X)) - a‖ ≤
    t * ‖X * a - a * X‖
  calc
    _ ≤ ‖X * a - a * X‖ * t := h'
    _ = _ := mul_comm _ _

theorem norm_exp_conjugation_sub_le_comm
    (b : selfAdjoint A) (a : A) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖exp (t • (Complex.I • (b : A))) * a *
      exp (t • (-(Complex.I • (b : A)))) - a‖ ≤
      t * ‖(b : A) * a - a * (b : A)‖ := by
  have h := norm_exp_conjugation_sub_le b a t ht
  have hc : (Complex.I • (b : A)) * a - a * (Complex.I • (b : A)) =
      Complex.I • ((b : A) * a - a * (b : A)) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [hc, norm_smul, Complex.norm_I, one_mul] at h
  exact h

theorem norm_exp_pi_conjugation_sub_le_comm
    (b : selfAdjoint A) (a : A) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖exp (t • (Complex.I • (((Real.pi : ℝ) • b : selfAdjoint A) : A))) * a *
      exp (t • (-(Complex.I • (((Real.pi : ℝ) • b : selfAdjoint A) : A)))) - a‖ ≤
      Real.pi * ‖(b : A) * a - a * (b : A)‖ := by
  have h := norm_exp_conjugation_sub_le_comm ((Real.pi : ℝ) • b) a t ht
  have hc : ‖(((Real.pi : ℝ) • b : selfAdjoint A) : A) * a -
      a * (((Real.pi : ℝ) • b : selfAdjoint A) : A)‖ =
      Real.pi * ‖(b : A) * a - a * (b : A)‖ := by
    change ‖((Real.pi : ℝ) • (b : A)) * a - a * ((Real.pi : ℝ) • (b : A))‖ = _
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc] at h
  have ht1 : t ≤ 1 := ht.2
  have hnonneg : 0 ≤ Real.pi * ‖(b : A) * a - a * (b : A)‖ :=
    mul_nonneg Real.pi_pos.le (norm_nonneg _)
  calc
    _ ≤ t * (Real.pi * ‖(b : A) * a - a * (b : A)‖) := h
    _ ≤ 1 * (Real.pi * ‖(b : A) * a - a * (b : A)‖) :=
      mul_le_mul_of_nonneg_right ht1 hnonneg
    _ = _ := one_mul _

theorem star_exp_I_selfAdjoint_smul (b : selfAdjoint A) (t : ℝ) :
    star (exp (t • (Complex.I • (b : A)))) =
      exp (t • (-(Complex.I • (b : A)))) := by
  rw [star_exp]
  have hx : star (t • (Complex.I • (b : A))) =
      t • (-(Complex.I • (b : A))) := by
    rw [star_smul, star_smul, b.property]
    simp
  rw [hx]

theorem expUnitary_smul_both_conjugations_le
    (b : selfAdjoint A) (a : A) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let u := selfAdjoint.expUnitary (t • b)
    ‖(u : A) * a * star (u : A) - a‖ ≤ t * ‖(b : A) * a - a * (b : A)‖ ∧
    ‖star (u : A) * a * (u : A) - a‖ ≤ t * ‖(b : A) * a - a * (b : A)‖ := by
  dsimp
  let u : unitary A := selfAdjoint.expUnitary (t • b)
  have hu : (u : A) = exp (t • (Complex.I • (b : A))) := by
    dsimp [u]
    rw [selfAdjoint.expUnitary_coe]
    congr 1
    change Complex.I • (t • (b : A)) = t • (Complex.I • (b : A))
    exact smul_comm Complex.I t (b : A)
  have hs : star (u : A) = exp (t • (-(Complex.I • (b : A)))) := by
    rw [hu, star_exp_I_selfAdjoint_smul]
  have hforward : ‖(u : A) * a * star (u : A) - a‖ ≤
      t * ‖(b : A) * a - a * (b : A)‖ := by
    rw [hu, star_exp_I_selfAdjoint_smul]
    exact norm_exp_conjugation_sub_le_comm b a t ht
  have hnormF : ‖(u : A) * a * star (u : A) - a‖ =
      ‖(u : A) * a - a * (u : A)‖ := by
    have heq : (u : A) * a * star (u : A) - a =
        ((u : A) * a - a * (u : A)) * star (u : A) := by
      have hunit : (u : A) * star (u : A) = 1 := u.property.2
      rw [sub_mul, mul_assoc, mul_assoc, hunit, mul_one]
    rw [heq]
    simpa using CStarRing.norm_mul_coe_unitary ((u : A) * a - a * (u : A)) (star u)
  have hnormI : ‖star (u : A) * a * (u : A) - a‖ =
      ‖(u : A) * a - a * (u : A)‖ := by
    have heq : star (u : A) * a * (u : A) - a =
        star (u : A) * (a * (u : A) - (u : A) * a) := by
      have hunit : star (u : A) * (u : A) = 1 := u.property.1
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hunit, one_mul, mul_assoc]
    rw [heq]
    calc
      _ = ‖a * (u : A) - (u : A) * a‖ := by
        simpa using CStarRing.norm_coe_unitary_mul (star u)
          (a * (u : A) - (u : A) * a)
      _ = _ := norm_sub_rev _ _
  exact ⟨hforward, by rw [hnormI, ← hnormF]; exact hforward⟩
end MathlibAnnex.Analysis.CStarAlgebra
