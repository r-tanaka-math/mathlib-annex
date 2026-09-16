import MathlibAnnex.Analysis.Normed.Operator.Determinant
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Strong L^n continuity of determinant integrals

The determinant estimate on continuous linear maps yields convergence of
integrals under strong L^n convergence. The source is an arbitrary measure
space; eventual L^n membership of the approximants is part of the hypothesis.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace MathlibAnnex.MeasureTheory

/-- Qualified strong L^n convergence over an arbitrary measure space. -/
def StrongLnOperatorField {n : ℕ} {α ι : Type*} [MeasurableSpace α]
    (l : Filter ι) (μ : Measure α)
    (P : ι → α → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (Q : α → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) : Prop :=
  Tendsto (fun i => eLpNorm (fun x => P i x - Q x) n μ) l (𝓝 0) ∧
    ∀ᶠ i in l, MemLp (P i) n μ

/-- Strong L^n convergence of square matrix fields implies convergence of
integrals of their determinants, over an arbitrary measure space. -/
theorem tendsto_integral_det_of_strongLn
    {n : ℕ} (hn : 0 < n) {α ι : Type*} [MeasurableSpace α]
    {l : Filter ι} {μ : Measure α}
    {P : ι → α → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
    {Q : α → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))}
    (hstrong : StrongLnOperatorField l μ P Q)
    (hQ : MemLp Q n μ) :
    Tendsto (fun i => ∫ x,
      LinearMap.det (P i x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∂μ) l
      (𝓝 (∫ x,
        LinearMap.det (Q x : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∂μ)) := by
  let det : (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) → ℝ) :=
    fun A => LinearMap.det (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  change Tendsto (fun i => ∫ x, det (P i x) ∂μ) l
    (𝓝 (∫ x, det (Q x) ∂μ))
  have hP : ∀ᶠ i in l, MemLp (P i) n μ := hstrong.2
  have hdiff : ∀ᶠ i in l, MemLp (fun x => P i x - Q x) n μ := by
    filter_upwards [hP] with i hi
    exact hi.sub hQ
  have hpoint : ∀ i x,
      ‖det (P i x) - det (Q x)‖ ≤
        n * (‖P i x‖ + ‖Q x‖) ^ (n - 1) * ‖P i x - Q x‖ := by
    intro i x
    simpa only [det, Fintype.card_fin] using
      MathlibAnnex.ContinuousLinearMap.norm_det_sub_le (P i x) (Q x)
  have hseminorm : Tendsto
      (fun i => eLpNorm (fun x => P i x - Q x) n μ) l (𝓝 0) :=
    hstrong.1
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hzero : det (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = 0 := by
    dsimp [det]
    rw [← LinearMap.det_toMatrix'
      (0 : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))]
    simpa using (Matrix.det_zero (inferInstance : Nonempty (Fin n)))
  have hdet_cont : Continuous det := by
    dsimp [det]
    exact ContinuousLinearMap.continuous_det
      (𝕜 := ℝ) (E := (Fin n → ℝ))
  have hdetQ_meas :
      AEStronglyMeasurable (fun x => det (Q x)) μ :=
    hdet_cont.comp_aestronglyMeasurable hQ.1
  have hdetQ_bound : ∀ x,
      ‖det (Q x)‖ ≤ (n : ℝ) * ‖Q x‖ ^ n := by
    intro x
    calc
      ‖det (Q x)‖ = ‖det (Q x) - det (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ := by
        rw [hzero, sub_zero]
      _ ≤ (n : ℝ) * (‖Q x‖ + ‖(0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖) ^ (n - 1) *
          ‖Q x - (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ := by
        simpa only [det, Fintype.card_fin] using
          MathlibAnnex.ContinuousLinearMap.norm_det_sub_le (Q x)
            (0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
      _ = (n : ℝ) * ‖Q x‖ ^ n := by
        simp only [norm_zero, add_zero, sub_zero]
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  have hdetQ : Integrable (fun x => det (Q x)) μ := by
    have hdom : Integrable (fun x => (n : ℝ) * ‖Q x‖ ^ n) μ :=
      (hQ.integrable_norm_pow hn.ne').const_mul n
    refine' hdom.mono' hdetQ_meas (ae_of_all μ fun x => _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n)
      (pow_nonneg (norm_nonneg _) n))] using hdetQ_bound x
  by_cases hn1 : n = 1
  · subst n
    have hDmem : ∀ᶠ i in l,
        MemLp (fun x => det (P i x) - det (Q x)) 1 μ := by
      filter_upwards [hP, hdiff] with i hi hdi
      have hdi1 : MemLp (fun x => P i x - Q x) 1 μ := by simpa using hdi
      refine' ⟨(hdet_cont.comp_aestronglyMeasurable hi.1).sub
        (hdet_cont.comp_aestronglyMeasurable hQ.1), _⟩
      refine' lt_of_le_of_lt (eLpNorm_mono fun x => _) hdi1.2
      simpa only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero] using hpoint i x
    have hDnorm : Tendsto
        (fun i => eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ)
        l (𝓝 0) := by
      have hseminorm1 : Tendsto
          (fun i => eLpNorm (fun x => P i x - Q x) 1 μ) l (𝓝 0) := by
        simpa using hseminorm
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hseminorm1
      · intro i
        exact bot_le
      · intro i
        exact eLpNorm_mono fun x => by
          simpa only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero] using hpoint i x
    have hIntD : Tendsto
        (fun i => ∫ x, det (P i x) - det (Q x) ∂μ) l (𝓝 0) := by
      refine' squeeze_zero_norm'
        (a := fun i => (eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ).toReal)
        _ _
      · filter_upwards [hDmem] with i hi
        refine' (norm_integral_le_integral_norm _).trans_eq _
        have heq := hi.eLpNorm_eq_integral_rpow_norm
          (one_ne_zero : (1 : ℝ≥0∞) ≠ 0) ENNReal.one_ne_top
        have heq' : eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ =
            ENNReal.ofReal (∫ x, ‖det (P i x) - det (Q x)‖ ∂μ) := by
          simpa only [ENNReal.toReal_one, Real.rpow_one, inv_one] using heq
        rw [heq', ENNReal.toReal_ofReal]
        exact integral_nonneg_of_ae (Eventually.of_forall fun x => norm_nonneg _)
      · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDnorm
    have hdetP : ∀ᶠ i in l, Integrable (fun x => det (P i x)) μ := by
      filter_upwards [hDmem] with i hi
      have hDi : Integrable (fun x => det (P i x) - det (Q x)) μ :=
        memLp_one_iff_integrable.mp hi
      have hfun : (fun x => det (P i x)) =
          (fun x => det (P i x) - det (Q x)) + (fun x => det (Q x)) := by
        funext x
        exact (sub_add_cancel (det (P i x)) (det (Q x))).symm
      rw [hfun]
      exact hDi.add hdetQ
    change Tendsto (fun i => ∫ x, det (P i x) ∂μ) l
      (𝓝 (∫ x, det (Q x) ∂μ))
    have hconst : Tendsto (fun _ : ι => ∫ x, det (Q x) ∂μ) l
        (𝓝 (∫ x, det (Q x) ∂μ)) := tendsto_const_nhds
    have ht := hconst.add hIntD
    have ht' : Tendsto (fun i => ∫ x, det (P i x) ∂μ) l
        (𝓝 ((∫ x, det (Q x) ∂μ) + 0)) := by
      apply ht.congr'
      filter_upwards [hdetP] with i hi
      rw [integral_sub hi hdetQ]
      ring
    simpa only [add_zero] using ht'
  · have hn2 : 1 < n := by omega
    let p : ℝ≥0∞ := ENNReal.conjExponent n
    letI hnconj : ENNReal.HolderConjugate (n : ℝ≥0∞) p := by
      dsimp [p]
      exact ENNReal.HolderConjugate.conjExponent (by exact_mod_cast hn)
    have hp_mul : p * (n - 1 : ℕ) = (n : ℝ≥0∞) := by
      dsimp [p]
      rw [show ((n - 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) - 1 by
        simp]
      rw [ENNReal.conjExponent, add_mul, one_mul,
        ENNReal.inv_mul_cancel, tsub_add_cancel_of_le]
      · exact_mod_cast hn
      · exact (tsub_pos_iff_lt.mpr (by exact_mod_cast hn2)).ne'
      · finiteness
    have hbound : ∀ᶠ i in l,
        eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ ≤
          (n : ℝ≥0∞) *
            (eLpNorm (fun x => P i x - Q x) n μ +
              eLpNorm Q n μ + eLpNorm Q n μ) ^ (n - 1) *
            eLpNorm (fun x => P i x - Q x) n μ := by
      filter_upwards [hP, hdiff] with i hi hdi
      let A : α → ℝ := fun x => ‖P i x‖ + ‖Q x‖
      let d : α → ℝ := fun x => ‖P i x - Q x‖
      have hA : MemLp A n μ := by
        dsimp [A]
        exact hi.norm.add hQ.norm
      have hd : MemLp d n μ := by
        dsimp [d]
        exact hdi.norm
      have hpow_meas : AEStronglyMeasurable (fun x => A x ^ (n - 1)) μ :=
        hA.1.pow (n - 1)
      have hpow_norm :
          eLpNorm (fun x => A x ^ (n - 1)) p μ = eLpNorm A n μ ^ (n - 1) := by
        let q : ℝ := (n - 1 : ℕ)
        have hqpos : 0 < q := by
          dsimp [q]
          exact_mod_cast Nat.sub_pos_of_lt hn2
        have hqE : ENNReal.ofReal q = (n - 1 : ℕ) := by
          dsimp [q]
          simp
        have hr := eLpNorm_norm_rpow (μ := μ) (p := p) (q := q) A hqpos
        rw [hqE, hp_mul] at hr
        have hpowfun : (fun x => ‖A x‖ ^ q) = (fun x => A x ^ q) := by
          funext x
          rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        rw [hpowfun] at hr
        simpa only [q, Real.rpow_natCast, ENNReal.rpow_natCast] using hr
      have hholder :
          eLpNorm (fun x => A x ^ (n - 1) * d x) 1 μ ≤
            eLpNorm A n μ ^ (n - 1) * eLpNorm (fun x => P i x - Q x) n μ := by
        calc
          eLpNorm (fun x => A x ^ (n - 1) * d x) 1 μ ≤
              eLpNorm (fun x => A x ^ (n - 1)) p μ * eLpNorm d n μ := by
            have hh := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
                (p := p) (q := (n : ℝ≥0∞)) (r := 1) (μ := μ)
                hpow_meas hd.1 (fun a b : ℝ => a * b) 1
                (ae_of_all μ fun x => by
                  simpa only [NNReal.coe_one, one_mul] using
                    (norm_mul (A x ^ (n - 1)) (d x)).le)
            change eLpNorm (fun x => A x ^ (n - 1) * d x) 1 μ ≤
              (1 : ℝ≥0∞) * eLpNorm (fun x => A x ^ (n - 1)) p μ * eLpNorm d n μ at hh
            simpa only [one_mul] using hh
          _ = eLpNorm A n μ ^ (n - 1) *
              eLpNorm (fun x => P i x - Q x) n μ := by
            rw [hpow_norm]
            simp only [d, eLpNorm_norm]
      have hA_le : eLpNorm A n μ ≤
          eLpNorm (fun x => P i x - Q x) n μ + eLpNorm Q n μ + eLpNorm Q n μ := by
        let B : α → ℝ := fun x => ‖P i x - Q x‖ + ‖Q x‖ + ‖Q x‖
        have hB : MemLp B n μ := by
          dsimp [B]
          exact (hdi.norm.add hQ.norm).add hQ.norm
        calc
          eLpNorm A n μ ≤ eLpNorm B n μ := by
            apply eLpNorm_mono
            intro x
            dsimp [A, B]
            have hp : ‖P i x‖ ≤ ‖P i x - Q x‖ + ‖Q x‖ := by
              calc
                ‖P i x‖ = ‖(P i x - Q x) + Q x‖ := by rw [sub_add_cancel]
                _ ≤ _ := norm_add_le _ _
            have hleft : 0 ≤ ‖P i x‖ + ‖Q x‖ :=
              add_nonneg (norm_nonneg _) (norm_nonneg _)
            have hright : 0 ≤ ‖P i x - Q x‖ + ‖Q x‖ + ‖Q x‖ :=
              add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
            rw [abs_of_nonneg hleft, abs_of_nonneg hright]
            simpa only [add_assoc, add_comm, add_left_comm] using
              (add_le_add_right hp ‖Q x‖)
          _ ≤ eLpNorm (fun x => ‖P i x - Q x‖ + ‖Q x‖) n μ +
              eLpNorm (fun x => ‖Q x‖) n μ := by
            dsimp [B]
            exact eLpNorm_add_le (p := (n : ℝ≥0∞)) (μ := μ)
              (hdi.norm.add hQ.norm).1 hQ.norm.1 (by exact_mod_cast hn)
          _ ≤ (eLpNorm (fun x => ‖P i x - Q x‖) n μ +
              eLpNorm (fun x => ‖Q x‖) n μ) + eLpNorm (fun x => ‖Q x‖) n μ := by
            have htri := eLpNorm_add_le (p := (n : ℝ≥0∞)) (μ := μ)
              hdi.norm.1 hQ.norm.1 (by exact_mod_cast hn)
            calc
              eLpNorm (fun x => ‖P i x - Q x‖ + ‖Q x‖) n μ +
                    eLpNorm (fun x => ‖Q x‖) n μ =
                  eLpNorm (fun x => ‖Q x‖) n μ +
                    eLpNorm (fun x => ‖P i x - Q x‖ + ‖Q x‖) n μ := add_comm _ _
              _ ≤ eLpNorm (fun x => ‖Q x‖) n μ +
                    (eLpNorm (fun x => ‖P i x - Q x‖) n μ +
                      eLpNorm (fun x => ‖Q x‖) n μ) := add_le_add le_rfl htri
              _ = (eLpNorm (fun x => ‖P i x - Q x‖) n μ +
                    eLpNorm (fun x => ‖Q x‖) n μ) +
                      eLpNorm (fun x => ‖Q x‖) n μ := by
                    simp only [add_comm]
          _ = _ := by simp only [eLpNorm_norm]
      calc
        eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ ≤
            eLpNorm (fun x => (n : ℝ) * (A x ^ (n - 1) * d x)) 1 μ := by
          apply eLpNorm_mono
          intro x
          have hnonneg : 0 ≤ (n : ℝ) * (A x ^ (n - 1) * d x) := by
            exact mul_nonneg (Nat.cast_nonneg n)
              (mul_nonneg
                (pow_nonneg (by
                  dsimp [A]
                  exact add_nonneg (norm_nonneg _) (norm_nonneg _)) (n - 1))
                (by
                  dsimp [d]
                  exact norm_nonneg _))
          rw [Real.norm_of_nonneg hnonneg]
          simpa only [A, d, mul_assoc] using hpoint i x
        _ = (n : ℝ≥0∞) * eLpNorm (fun x => A x ^ (n - 1) * d x) 1 μ := by
          have hfun : (fun x => (n : ℝ) * (A x ^ (n - 1) * d x)) =
              n • (fun x => A x ^ (n - 1) * d x) := by
            funext x
            simp [Pi.smul_apply, nsmul_eq_mul]
          rw [hfun]
          exact eLpNorm_nsmul (p := (1 : ℝ≥0∞)) (μ := μ) n
            (fun x => A x ^ (n - 1) * d x)
        _ ≤ (n : ℝ≥0∞) *
            (eLpNorm A n μ ^ (n - 1) * eLpNorm (fun x => P i x - Q x) n μ) := by
          exact mul_le_mul' le_rfl hholder
        _ ≤ (n : ℝ≥0∞) *
            ((eLpNorm (fun x => P i x - Q x) n μ + eLpNorm Q n μ +
              eLpNorm Q n μ) ^ (n - 1) *
                eLpNorm (fun x => P i x - Q x) n μ) := by
          exact mul_le_mul' le_rfl
            (mul_le_mul' (pow_le_pow_left' hA_le (n - 1)) le_rfl)
        _ = _ := by simp only [mul_assoc]
    have hmajor : Tendsto
        (fun i => (n : ℝ≥0∞) *
          (eLpNorm (fun x => P i x - Q x) n μ + eLpNorm Q n μ + eLpNorm Q n μ) ^
            (n - 1) * eLpNorm (fun x => P i x - Q x) n μ)
        l (𝓝 0) := by
      let q : ℝ≥0∞ := eLpNorm Q n μ
      let C : ℝ≥0∞ := (n : ℝ≥0∞) * (1 + q + q) ^ (n - 1)
      have hd_le_one : ∀ᶠ i in l,
          eLpNorm (fun x => P i x - Q x) n μ ≤ 1 := by
        have hlt := (tendsto_order.1 hseminorm).2 (1 : ℝ≥0∞)
          (show (0 : ℝ≥0∞) < 1 from zero_lt_one)
        exact hlt.mono fun i hi => hi.le
      have hC_ne_top : C ≠ ⊤ := by
        dsimp [C, q]
        finiteness [hQ.2]
      have hcontrolled : ∀ᶠ i in l,
          (n : ℝ≥0∞) *
              (eLpNorm (fun x => P i x - Q x) n μ + eLpNorm Q n μ + eLpNorm Q n μ) ^
                (n - 1) * eLpNorm (fun x => P i x - Q x) n μ ≤
            C * eLpNorm (fun x => P i x - Q x) n μ := by
        filter_upwards [hd_le_one] with i hi
        dsimp [C, q]
        exact mul_le_mul'
          (mul_le_mul' le_rfl
            (pow_le_pow_left'
              (add_le_add (add_le_add hi le_rfl) le_rfl) (n - 1)))
          le_rfl
      have hCmul : Tendsto
          (fun i => C * eLpNorm (fun x => P i x - Q x) n μ) l (𝓝 0) := by
        simpa only [mul_zero] using
          ENNReal.Tendsto.const_mul hseminorm (Or.inr hC_ne_top)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCmul
      · exact Eventually.of_forall fun i => bot_le
      · exact hcontrolled
    have hDnorm : Tendsto
        (fun i => eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ)
        l (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
      · exact Eventually.of_forall fun i => bot_le
      · exact hbound
    have hDmem : ∀ᶠ i in l,
        MemLp (fun x => det (P i x) - det (Q x)) 1 μ := by
      filter_upwards [hP, hbound, hdiff] with i hi hib hdi
      refine' ⟨(hdet_cont.comp_aestronglyMeasurable hi.1).sub hdetQ_meas, _⟩
      refine' lt_of_le_of_lt hib _
      finiteness [hQ.2, hdi.2]
    have hIntD : Tendsto
        (fun i => ∫ x, det (P i x) - det (Q x) ∂μ) l (𝓝 0) := by
      refine' squeeze_zero_norm'
        (a := fun i => (eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ).toReal)
        _ _
      · filter_upwards [hDmem] with i hi
        refine' (norm_integral_le_integral_norm _).trans_eq _
        have heq := hi.eLpNorm_eq_integral_rpow_norm
          (one_ne_zero : (1 : ℝ≥0∞) ≠ 0) ENNReal.one_ne_top
        have heq' : eLpNorm (fun x => det (P i x) - det (Q x)) 1 μ =
            ENNReal.ofReal (∫ x, ‖det (P i x) - det (Q x)‖ ∂μ) := by
          simpa only [ENNReal.toReal_one, Real.rpow_one, inv_one] using heq
        have hto := congrArg ENNReal.toReal heq'
        have hnonneg : 0 ≤ ∫ x, ‖det (P i x) - det (Q x)‖ ∂μ :=
          integral_nonneg_of_ae (Eventually.of_forall fun x => norm_nonneg _)
        rw [ENNReal.toReal_ofReal hnonneg] at hto
        exact hto.symm
      · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDnorm
    have hdetP : ∀ᶠ i in l, Integrable (fun x => det (P i x)) μ := by
      filter_upwards [hDmem] with i hi
      have hDi : Integrable (fun x => det (P i x) - det (Q x)) μ :=
        memLp_one_iff_integrable.mp hi
      have hfun : (fun x => det (P i x)) =
          (fun x => det (P i x) - det (Q x)) + (fun x => det (Q x)) := by
        funext x
        exact (sub_add_cancel (det (P i x)) (det (Q x))).symm
      rw [hfun]
      exact hDi.add hdetQ
    change Tendsto (fun i => ∫ x, det (P i x) ∂μ) l
      (𝓝 (∫ x, det (Q x) ∂μ))
    have hconst : Tendsto (fun _ : ι => ∫ x, det (Q x) ∂μ) l
        (𝓝 (∫ x, det (Q x) ∂μ)) := tendsto_const_nhds
    have ht := hconst.add hIntD
    have ht' : Tendsto (fun i => ∫ x, det (P i x) ∂μ) l
        (𝓝 ((∫ x, det (Q x) ∂μ) + 0)) := by
      apply ht.congr'
      filter_upwards [hdetP] with i hi
      rw [integral_sub hi hdetQ]
      ring
    simpa only [add_zero] using ht'

end MathlibAnnex.MeasureTheory
