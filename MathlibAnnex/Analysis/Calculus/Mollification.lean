import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic

/-!
# Strong local convergence of mollified derivatives

Derivatives of a globally Lipschitz map converge in the original dimension
exponent on compact sets. The conclusion records both seminorm convergence
and eventual membership in the corresponding Lp space.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Convolution Topology ENNReal NNReal Pointwise
namespace MathlibAnnex
namespace Mollification

noncomputable def standardMollifier {n : ℕ} (ε : ℝ) : (Fin n → ℝ) → ℝ :=
  let φ : ContDiffBump (0 : (Fin n → ℝ)) :=
    if hε : 0 < ε then
      { rIn := ε / 2
        rOut := ε
        rIn_pos := by positivity
        rIn_lt_rOut := by nlinarith }
    else
      { rIn := (1 : ℝ) / 2
        rOut := 1
        rIn_pos := by norm_num
        rIn_lt_rOut := by norm_num }
  φ.normed volume

noncomputable def mollify {n N : ℕ} (ε : ℝ)
    (f : (Fin n → ℝ) → (Fin N → ℝ)) : (Fin n → ℝ) → (Fin N → ℝ) :=
  standardMollifier ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
open scoped Pointwise

theorem standardMollifier_hasCompactSupport {n : ℕ} (ε : ℝ) :
    HasCompactSupport (standardMollifier (n := n) ε) := by
  unfold standardMollifier
  split_ifs <;> exact ContDiffBump.hasCompactSupport_normed _

theorem standardMollifier_continuous {n : ℕ} (ε : ℝ) :
    Continuous (standardMollifier (n := n) ε) := by
  unfold standardMollifier
  split_ifs <;>
    exact (ContDiffBump.contDiff_normed (n := (⊤ : ℕ∞)) _).continuous

theorem mollify_add {n N : ℕ} (ε : ℝ)
    (f g : (Fin n → ℝ) → (Fin N → ℝ))
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    mollify ε (fun x => f x + g x) =
      fun x => mollify ε f x + mollify ε g x := by

  funext x
  have hcf := standardMollifier_hasCompactSupport (n := n) ε
  have hcont := standardMollifier_continuous (n := n) ε
  have hif := hcf.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hcont hf
  have hig := hcf.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hcont hg
  simp only [mollify, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_add]
  exact MeasureTheory.integral_add (hif x).integrable (hig x).integrable

theorem mollify_contDiff {n N : ℕ} {ε : ℝ} (hε : 0 < ε)
    {f : (Fin n → ℝ) → (Fin N → ℝ)} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mollify ε f) := by

  let φ : ContDiffBump (0 : (Fin n → ℝ)) :=
    { rIn := ε / 2
      rOut := ε
      rIn_pos := by positivity
      rIn_lt_rOut := by nlinarith }
  have hstd : standardMollifier (n := n) ε = φ.normed volume := by
    simp [standardMollifier, φ, hε]
  rw [mollify, hstd]
  exact (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.contDiff_normed (n := (⊤ : ℕ∞))) hf

theorem eventually_tsupport_mollify_subset_compact
    {n N : ℕ} {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : HasCompactSupport u) :
    ∃ K : Set ((Fin n → ℝ)), IsCompact K ∧ tsupport u ⊆ K ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), tsupport (mollify ε u) ⊆ K := by

  rcases (Metric.isBounded_iff_subset_closedBall (0 : (Fin n → ℝ))).mp
      hu.isCompact.isBounded with ⟨R, hR⟩
  let K : Set ((Fin n → ℝ)) := Metric.closedBall 0 (R + 1)
  refine ⟨K, ProperSpace.isCompact_closedBall _ _, ?_, ?_⟩
  · intro x hx
    exact Metric.mem_closedBall'.2
      (le_trans (Metric.mem_closedBall'.1 (hR hx)) (by linarith))
  · have hone : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (isOpen_Iio.mem_nhds (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hone] with ε hε hε1
    have hεpos : 0 < ε := hε
    let φ : ContDiffBump (0 : (Fin n → ℝ)) :=
      { rIn := ε / 2
        rOut := ε
        rIn_pos := by positivity
        rIn_lt_rOut := by nlinarith }
    have hstd : standardMollifier (n := n) ε = φ.normed volume := by
      simp [standardMollifier, φ, hεpos]
    unfold tsupport
    apply closure_minimal
    · intro x hx
      rcases (MeasureTheory.support_convolution_subset
        (ContinuousLinearMap.lsmul ℝ ℝ) hx) with ⟨a, ha, b, hb, rfl⟩
      rw [hstd, φ.support_normed_eq] at ha
      have ha' : ‖a‖ < ε := by
        simpa only [Metric.mem_ball, dist_zero_right] using ha
      have hb' : ‖b‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hR (subset_closure hb)
      change a + b ∈ Metric.closedBall (0 : (Fin n → ℝ)) (R + 1)
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (norm_add_le a b) (by linarith)
    · exact Metric.isClosed_closedBall

theorem eventually_mollify_fderiv_memLpOn_compact
    {m N : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set ((Fin (m + 1) → ℝ))} (hK : IsCompact K) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      MemLp (fun x => fderiv ℝ (mollify ε f) x)
        (m + 1) (volume.restrict K) := by

  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hLip := hf
  have hsmooth := mollify_contDiff hεpos hLip.continuous.locallyIntegrable
  have hDcont : Continuous (fun x => fderiv ℝ (mollify ε f) x) :=
    hsmooth.continuous_fderiv (by simp)
  have hnormcont : Continuous (fun x => ‖fderiv ℝ (mollify ε f) x‖) :=
    continuous_norm.comp hDcont
  have hbdd : BddAbove ((fun x => ‖fderiv ℝ (mollify ε f) x‖) '' K) :=
    (hK.image hnormcont).isBounded.bddAbove
  rcases hbdd with ⟨B, hB⟩
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound hDcont.stronglyMeasurable.aestronglyMeasurable B
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hB ⟨x, hx, rfl⟩

theorem tendsto_eLpNorm_fderiv_mollify_sub
    {m N : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set ((Fin (m + 1) → ℝ))} (hK : IsCompact K) :
    (Tendsto (fun ε => eLpNorm
      (fun x => fderiv ℝ (mollify ε f) x - fderiv ℝ f x)
      ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp
        (fun x => fderiv ℝ (mollify ε f) x) ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
  constructor
  · classical
    have hLip := hf
    have hdiff : ∀ᵐ z ∂volume, DifferentiableAt ℝ f z :=
      hLip.ae_differentiableAt
    have hderiv (ε : ℝ) (hε : 0 < ε) (x₀ : (Fin (m + 1) → ℝ)) :
        fderiv ℝ (mollify ε f) x₀ =
          ∫ y : (Fin (m + 1) → ℝ),
            standardMollifier ε y • fderiv ℝ f (x₀ - y) := by
      let φ : ContDiffBump (0 : (Fin (m + 1) → ℝ)) :=
        { rIn := ε / 2
          rOut := ε
          rIn_pos := by positivity
          rIn_lt_rOut := by nlinarith }
      have hstd : standardMollifier (n := m + 1) ε = φ.normed volume := by
        simp [standardMollifier, φ, hε]
      have hk : Integrable (standardMollifier (n := m + 1) ε) volume := by
        rw [hstd]
        exact φ.integrable_normed
      have hkc : HasCompactSupport
          (standardMollifier (n := m + 1) ε) := by
        rw [hstd]
        exact φ.hasCompactSupport_normed
      have hkcont : Continuous
          (standardMollifier (n := m + 1) ε) := by
        rw [hstd]
        exact (φ.contDiff_normed (μ := volume) (n := (1 : ℕ∞))).continuous
      have hconv : ∀ x : (Fin (m + 1) → ℝ), Integrable
          (fun y : (Fin (m + 1) → ℝ) =>
            standardMollifier ε y • f (x - y)) volume := by
        intro x
        exact (hkc.convolutionExists_left
          (ContinuousLinearMap.lsmul ℝ ℝ) hkcont
          hLip.continuous.locallyIntegrable) x
      have hdiffx : ∀ᵐ y ∂volume, DifferentiableAt ℝ f (x₀ - y) :=
        (MeasureTheory.Measure.measurePreserving_sub_left volume x₀).quasiMeasurePreserving.ae
          hdiff
      have hparam := hasFDerivAt_integral_of_dominated_loc_of_lip'
        (μ := volume)
        (F := fun x y : (Fin (m + 1) → ℝ) =>
          standardMollifier ε y • f (x - y))
        (F' := fun y : (Fin (m + 1) → ℝ) =>
          standardMollifier ε y • fderiv ℝ f (x₀ - y))
        (bound := fun y : (Fin (m + 1) → ℝ) =>
          ‖standardMollifier ε y‖ * (C : ℝ))
        (s := Set.univ) (x₀ := x₀)
        (show Set.univ ∈ nhds x₀ from univ_mem)
        (by intro x hx; exact (hconv x).aestronglyMeasurable)
        (hconv x₀)
        (by
          have hmfd : AEStronglyMeasurable
              (fun y : (Fin (m + 1) → ℝ) => fderiv ℝ f (x₀ - y)) volume := by
            exact (((measurable_fderiv ℝ f).comp
              (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable
          exact hk.aestronglyMeasurable.smul hmfd)
        (by
          filter_upwards with y
          intro x hx
          rw [← smul_sub, norm_smul]
          have hb : ‖f (x - y) - f (x₀ - y)‖ ≤
              (C : ℝ) * ‖(x - y) - (x₀ - y)‖ := by
            simpa only [dist_eq_norm] using
              hLip.dist_le_mul (x - y) (x₀ - y)
          calc
            ‖standardMollifier ε y‖ * ‖f (x - y) - f (x₀ - y)‖ ≤
                ‖standardMollifier ε y‖ *
                  ((C : ℝ) * ‖x - x₀‖) := by
                    gcongr
                    simpa only [show (x - y) - (x₀ - y) = x - x₀ by module] using hb
            _ = (‖standardMollifier ε y‖ * (C : ℝ)) *
                  ‖x - x₀‖ := by ring)
        (hk.norm.mul_const (C : ℝ))
        (by
          filter_upwards [hdiffx] with y hy
          have hsub : HasFDerivAt (fun x : (Fin (m + 1) → ℝ) => x - y)
              (ContinuousLinearMap.id ℝ ((Fin (m + 1) → ℝ))) x₀ := by
            exact (hasFDerivAt_id (𝕜 := ℝ) x₀).sub_const y
          have hc := hy.hasFDerivAt.comp x₀ hsub
          have hc' : HasFDerivAt (fun x : (Fin (m + 1) → ℝ) => f (x - y))
              (fderiv ℝ f (x₀ - y)) x₀ := by
            change HasFDerivAt (f ∘ fun x : (Fin (m + 1) → ℝ) => x - y)
              (fderiv ℝ f (x₀ - y)) x₀
            simpa only [ContinuousLinearMap.comp_id] using hc
          exact hc'.const_smul (standardMollifier ε y))
      have hd := hparam.2.fderiv
      change fderiv ℝ (fun x : (Fin (m + 1) → ℝ) =>
        ∫ y : (Fin (m + 1) → ℝ), standardMollifier ε y • f (x - y)) x₀ = _
      exact hd
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall
      (0 : (Fin (m + 1) → ℝ))
    let S : Set ((Fin (m + 1) → ℝ)) :=
      Metric.closedBall 0 (max R 0 + 1)
    have hKS : K ⊆ S := by
      intro x hx
      have hxR : ‖x‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hx
      have hxS : ‖x‖ ≤ max R 0 + 1 :=
        hxR.trans (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))
      simpa only [S, Metric.mem_closedBall, dist_zero_right] using hxS
    have hScompact : IsCompact S := by
      exact isCompact_closedBall (0 : (Fin (m + 1) → ℝ)) (max R 0 + 1)
    have hSmeas : MeasurableSet S := hScompact.measurableSet
    have hSfin : volume S < ∞ := hScompact.measure_lt_top
    let entry (i : Fin (m + 1)) (j : Fin N) :
        ((Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.apply ℝ ((Fin N → ℝ)) (Pi.single i 1))
    let q (i : Fin (m + 1)) (j : Fin N) : (Fin (m + 1) → ℝ) → ℝ :=
      S.indicator (fun x => entry i j (fderiv ℝ f x))
    have hentry_meas (i : Fin (m + 1)) (j : Fin N) :
        StronglyMeasurable (fun x : (Fin (m + 1) → ℝ) =>
          entry i j (fderiv ℝ f x)) := by
      exact ((entry i j).continuous.measurable.comp
        (measurable_fderiv ℝ f)).stronglyMeasurable
    have hq (i : Fin (m + 1)) (j : Fin N) :
        MemLp (q i j) ((m + 1 : ℕ) : ℝ≥0∞) volume := by
      letI : IsFiniteMeasure (volume.restrict S) :=
        ⟨by simpa using hSfin⟩
      have hlocal : MemLp (fun x : (Fin (m + 1) → ℝ) =>
          entry i j (fderiv ℝ f x)) ((m + 1 : ℕ) : ℝ≥0∞)
            (volume.restrict S) := by
        apply MemLp.of_bound (hentry_meas i j).aestronglyMeasurable
          (‖entry i j‖ * (C : ℝ))
        filter_upwards with x
        calc
          ‖entry i j (fderiv ℝ f x)‖ ≤
              ‖entry i j‖ * ‖fderiv ℝ f x‖ :=
            (entry i j).le_opNorm _
          _ ≤ ‖entry i j‖ * (C : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg (entry i j))
      constructor
      · exact ((hentry_meas i j).indicator hSmeas).aestronglyMeasurable
      · change eLpNorm
          (S.indicator (fun x => entry i j (fderiv ℝ f x)))
            ((m + 1 : ℕ) : ℝ≥0∞) volume < ∞
        rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
        exact hlocal.eLpNorm_lt_top
    letI : Fact (1 ≤ ((m + 1 : ℕ) : ℝ≥0∞)) :=
      ⟨by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)⟩
    letI : Fact (((m + 1 : ℕ) : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
    have hcoord_full (i : Fin (m + 1)) (j : Fin N) :
        Tendsto
          (fun ε => eLpNorm
            (fun x =>
              ((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            ((m + 1 : ℕ) : ℝ≥0∞) volume)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      let p : ℝ≥0∞ := ((m + 1 : ℕ) : ℝ≥0∞)
      let B : ℝ := ‖entry i j‖ * (C : ℝ)
      have hB : 0 ≤ B :=
        mul_nonneg (norm_nonneg (entry i j)) C.coe_nonneg
      have hq_bound (x : (Fin (m + 1) → ℝ)) : ‖q i j x‖ ≤ B := by
        by_cases hx : x ∈ S
        · simp only [q, Set.indicator_of_mem hx]
          calc
            ‖entry i j (fderiv ℝ f x)‖ ≤
                ‖entry i j‖ * ‖fderiv ℝ f x‖ := (entry i j).le_opNorm _
            _ ≤ B := by
              exact mul_le_mul_of_nonneg_left
                (norm_fderiv_le_of_lipschitz ℝ hLip)
                (norm_nonneg (entry i j))
        · simp only [q]
          simp [hx]
          exact hB
      have hqsupp : Function.support (q i j) ⊆ S := by
        intro x hx
        by_contra hxS
        simp [q, hxS] at hx
      let T : Set ((Fin (m + 1) → ℝ)) := Metric.closedBall 0 (max R 0 + 2)
      have hTcompact : IsCompact T :=
        ProperSpace.isCompact_closedBall _ _
      have hTmeas : MeasurableSet T := hTcompact.measurableSet
      have hTfin : volume T < ∞ := hTcompact.measure_lt_top
      let φ (ε : ℝ) : ContDiffBump (0 : (Fin (m + 1) → ℝ)) :=
        if hε : 0 < ε then
          { rIn := ε / 2
            rOut := ε
            rIn_pos := by positivity
            rIn_lt_rOut := by nlinarith }
        else
          { rIn := (1 : ℝ) / 2
            rOut := 1
            rIn_pos := by norm_num
            rIn_lt_rOut := by norm_num }
      have hstd (ε : ℝ) (hε : 0 < ε) :
          standardMollifier (n := m + 1) ε = (φ ε).normed volume := by
        simp [standardMollifier, φ, hε]
      have hrout : Tendsto (fun ε => (φ ε).rOut)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have heq : (fun ε => (φ ε).rOut) =ᶠ[
            nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun ε => ε) := by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          have hε' : 0 < ε := hε
          simp [φ, hε']
        exact (tendsto_id.mono_left inf_le_left).congr' heq.symm
      have hratio : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (φ ε).rOut ≤ 2 * (φ ε).rIn := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : 0 < ε := hε
        simp [φ, hε']
        linarith
      have hqLI : LocallyIntegrable (q i j) volume :=
        (hq i j).locallyIntegrable Fact.out
      have haeφ : ∀ᵐ x ∂volume,
          Tendsto
            (fun ε => ((φ ε).normed volume) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j) $ x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (q i j x)) :=
        ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
          hrout hratio hqLI
      have hae : ∀ᵐ x ∂volume,
          Tendsto
            (fun ε => ((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (q i j x)) := by
        filter_upwards [haeφ] with x hx
        apply hx.congr'
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [hstd ε hε]
      have hST : S ⊆ T := by
        intro x hx
        have hx' : ‖x‖ ≤ max R 0 + 1 := by
          simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx
        simpa only [T, Metric.mem_closedBall, dist_zero_right] using
          (hx'.trans (by linarith))
      have hconv_cont (ε : ℝ) (hε : 0 < ε) : Continuous
          (((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) := by
        rw [hstd ε hε]
        exact ((φ ε).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
          (ContinuousLinearMap.lsmul ℝ ℝ)
          ((φ ε).contDiff_normed (n := (⊤ : ℕ∞))) hqLI |>.continuous
      have hdist (ε : ℝ) (hε : 0 < ε) (x : (Fin (m + 1) → ℝ)) :
          ‖((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x‖ ≤
            2 * B := by
        rw [hstd ε hε, ← dist_eq_norm]
        apply ContDiffBump.dist_normed_convolution_le (hq i j).1
        intro y hy
        rw [Real.dist_eq]
        calc
          |q i j y - q i j x| ≤ ‖q i j y‖ + ‖q i j x‖ :=
            abs_sub _ _
          _ ≤ B + B := add_le_add (hq_bound y) (hq_bound x)
          _ = 2 * B := by ring
      have hconv_supp (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
          Function.support (((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) ⊆ T := by
        intro x hx
        rcases (MeasureTheory.support_convolution_subset
          (ContinuousLinearMap.lsmul ℝ ℝ) hx) with ⟨a, ha, b, hb, rfl⟩
        rw [hstd ε hε, (φ ε).support_normed_eq] at ha
        have ha' : ‖a‖ < ε := by
          have hr : (φ ε).rOut = ε := by simp [φ, hε]
          simpa only [Metric.mem_ball, dist_zero_right, hr] using ha
        have hbS := hqsupp hb
        have hb' : ‖b‖ ≤ max R 0 + 1 := by
          simpa only [S, Metric.mem_closedBall, dist_zero_right] using hbS
        change a + b ∈ T
        simp only [T, Metric.mem_closedBall, dist_zero_right]
        exact le_trans (norm_add_le a b) (by linarith)
      have hzero_out (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
          {x : (Fin (m + 1) → ℝ)} (hx : x ∉ T) :
          ((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x = 0 := by
        have hc : ((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x = 0 := by
          by_contra hc
          exact hx (hconv_supp ε hε hε1 hc)
        have hqx : q i j x = 0 := by
          by_contra hqx
          exact hx (hST (hqsupp hqx))
        rw [hc, hqx, sub_zero]
      have hconv_mem (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
          MemLp (((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) p volume := by
        letI : IsFiniteMeasure (volume.restrict T) :=
          ⟨by simpa using hTfin⟩
        have hlocal : MemLp (((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) p
            (volume.restrict T) := by
          apply MemLp.of_bound (hconv_cont ε hε).stronglyMeasurable.aestronglyMeasurable
            (3 * B)
          filter_upwards with x
          have hd := hdist ε hε x
          have htri :
              ‖((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x‖ ≤
                ‖((standardMollifier ε) ⋆[
                  ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x‖ +
                  ‖q i j x‖ := by
            simpa only [sub_add_cancel] using
              norm_add_le
                (((standardMollifier ε) ⋆[
                  ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
                (q i j x)
          exact htri.trans (by linarith [hq_bound x])
        have hind : T.indicator (((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) =
            (((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j))) := by
          funext x
          by_cases hx : x ∈ T
          · simp [hx]
          · simp only [Set.indicator]
            simp [hx]
            by_contra hc
            exact hx (hconv_supp ε hε hε1 (Ne.symm hc))
        rw [← hind]
        exact (MeasureTheory.memLp_indicator_iff_restrict hTmeas).2 hlocal
      have hdiff_mem (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
          MemLp (fun x =>
            ((standardMollifier ε) ⋆[
              ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            p volume :=
        (hconv_mem ε hε hε1).sub (hq i j)
      let F (ε : ℝ) (x : (Fin (m + 1) → ℝ)) : ℝ :=
        ‖((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x‖ ^ (m + 1)
      let bound (x : (Fin (m + 1) → ℝ)) : ℝ :=
        T.indicator (fun _ => (2 * B) ^ (m + 1)) x
      have hbound_int : Integrable bound volume := by
        apply (MeasureTheory.integrable_indicator_iff hTmeas).2
        exact ContinuousOn.integrableOn_compact hTcompact
          (continuousOn_const : ContinuousOn
            (fun _ : (Fin (m + 1) → ℝ) => (2 * B) ^ (m + 1)) T)
      have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          0 < ε ∧ ε < 1 := by
        have hone : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
          Filter.Eventually.filter_mono inf_le_left
            (isOpen_Iio.mem_nhds (by norm_num))
        filter_upwards [self_mem_nhdsWithin, hone] with ε hε hε1
        exact ⟨hε, hε1⟩
      have hFmeas : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          AEStronglyMeasurable (F ε) volume := by
        filter_upwards [hsmall] with ε hε
        exact (hdiff_mem ε hε.1 hε.2).1.norm.pow (m + 1)
      have hFbound : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ᵐ x ∂volume, ‖F ε x‖ ≤ bound x := by
        filter_upwards [hsmall] with ε hε
        filter_upwards with x
        by_cases hx : x ∈ T
        · simp only [bound, Set.indicator_of_mem hx, F, norm_pow, norm_norm]
          exact pow_le_pow_left₀ (norm_nonneg _) (hdist ε hε.1 x) _
        · simp only [F]
          rw [hzero_out ε hε.1 hε.2 hx]
          simp [bound, hx]
      have hFlim : ∀ᵐ x ∂volume,
          Tendsto (fun ε => F ε x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        filter_upwards [hae] with x hx
        have hconst : Tendsto (fun _ : ℝ => q i j x)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (q i j x)) :=
          tendsto_const_nhds
        simpa only [F, sub_self, norm_zero, zero_pow (Nat.succ_ne_zero m)] using
          (hx.sub hconst).norm.pow (m + 1)
      have hInt : Tendsto (fun ε => ∫ x, F ε x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa only [integral_zero] using
          tendsto_integral_filter_of_dominated_convergence bound hFmeas hFbound
            hbound_int hFlim
      have hpReal : p.toReal = (m + 1 : ℝ) := by
        dsimp only [p]
        rw [ENNReal.toReal_natCast]
        norm_num
      have hnorm_eq : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          eLpNorm
              (fun x =>
                ((standardMollifier ε) ⋆[
                  ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
              p volume =
            ENNReal.ofReal ((∫ x, F ε x) ^ p.toReal⁻¹) := by
        filter_upwards [hsmall] with ε hε
        rw [(hdiff_mem ε hε.1 hε.2).eLpNorm_eq_integral_rpow_norm]
        · congr 2
          apply integral_congr_ae
          filter_upwards with x
          rw [hpReal]
          rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_num]
          exact Real.rpow_natCast _ (m + 1)
        · simp [p]
        · simp [p]
      have ha : 0 < p.toReal⁻¹ := by rw [hpReal]; positivity
      have hpow : Tendsto (fun z : ℝ => z ^ p.toReal⁻¹)
          (nhds 0) (nhds 0) := by
        simpa [Real.zero_rpow ha.ne'] using
          (Real.continuous_rpow_const ha.le).tendsto (0 : ℝ)
      have hof : Tendsto (fun z : ℝ => ENNReal.ofReal z)
          (nhds 0) (nhds 0) := by
        simpa using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      have hnormEq :
          (fun ε => eLpNorm
            (fun x =>
              ((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            p volume) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun ε => ENNReal.ofReal ((∫ x, F ε x) ^ p.toReal⁻¹)) := hnorm_eq
      exact (hof.comp (hpow.comp hInt)).congr' hnormEq.symm
    have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < ε ∧ ε < 1 := by
      have hone : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
        Filter.Eventually.filter_mono inf_le_left
          (isOpen_Iio.mem_nhds (by norm_num))
      filter_upwards [self_mem_nhdsWithin, hone] with ε hε hε1
      exact ⟨hε, hε1⟩
    have hscalar (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
        (i : Fin (m + 1)) (j : Fin N) (x : (Fin (m + 1) → ℝ)) (hx : x ∈ K) :
        entry i j (fderiv ℝ (mollify ε f) x - fderiv ℝ f x) =
          ((standardMollifier ε) ⋆[
            ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x := by
      let φ : ContDiffBump (0 : (Fin (m + 1) → ℝ)) :=
        { rIn := ε / 2
          rOut := ε
          rIn_pos := by positivity
          rIn_lt_rOut := by nlinarith }
      have hstd : standardMollifier (n := m + 1) ε = φ.normed volume := by
        simp [standardMollifier, φ, hε]
      have hk : Integrable (standardMollifier (n := m + 1) ε) volume := by
        rw [hstd]
        exact φ.integrable_normed
      have hInt : Integrable (fun y : (Fin (m + 1) → ℝ) =>
          standardMollifier ε y • fderiv ℝ f (x - y)) volume := by
        have hm : AEStronglyMeasurable (fun y : (Fin (m + 1) → ℝ) =>
            standardMollifier ε y • fderiv ℝ f (x - y)) volume := by
          have hmfd : AEStronglyMeasurable
              (fun y : (Fin (m + 1) → ℝ) => fderiv ℝ f (x - y)) volume := by
            exact (((measurable_fderiv ℝ f).comp
              (measurable_const.sub measurable_id)).stronglyMeasurable).aestronglyMeasurable
          exact hk.aestronglyMeasurable.smul hmfd
        apply (hk.norm.mul_const (C : ℝ)).mono' hm
        filter_upwards with y
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
      have hmove : entry i j (∫ y : (Fin (m + 1) → ℝ),
            standardMollifier ε y • fderiv ℝ f (x - y)) =
          ∫ y : (Fin (m + 1) → ℝ),
            entry i j (standardMollifier ε y • fderiv ℝ f (x - y)) :=
        ((entry i j).integral_comp_comm hInt).symm
      have hmem (y : (Fin (m + 1) → ℝ))
          (hy : standardMollifier ε y ≠ 0) : x - y ∈ S := by
        have hysupp : y ∈ Function.support (standardMollifier ε) := hy
        rw [hstd, φ.support_normed_eq] at hysupp
        have hyε : ‖y‖ < ε := by
          simpa only [Metric.mem_ball, dist_zero_right] using hysupp
        have hxR : ‖x‖ ≤ R := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hx
        have hxy : ‖x - y‖ ≤ max R 0 + 1 := by
          calc
            ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
            _ ≤ R + 1 := add_le_add hxR (le_of_lt (hyε.trans hε1))
            _ ≤ max R 0 + 1 := by gcongr; exact le_max_left R 0
        simpa only [S, Metric.mem_closedBall, dist_zero_right] using hxy
      have hconv : (∫ y : (Fin (m + 1) → ℝ),
            standardMollifier ε y * entry i j (fderiv ℝ f (x - y))) =
          ∫ y : (Fin (m + 1) → ℝ), standardMollifier ε y * q i j (x - y) := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : standardMollifier ε y = 0
        · simp only [hy, zero_mul]
        · simp only [q, Set.indicator_of_mem (hmem y hy)]
      have hqx : q i j x = entry i j (fderiv ℝ f x) := by
        simp only [q, Set.indicator_of_mem (hKS hx)]
      rw [map_sub, hderiv ε hε x, hmove]
      change (∫ y : (Fin (m + 1) → ℝ),
          standardMollifier ε y * entry i j (fderiv ℝ f (x - y))) -
            entry i j (fderiv ℝ f x) =
        (∫ y : (Fin (m + 1) → ℝ), standardMollifier ε y * q i j (x - y)) -
          q i j x
      rw [hconv, hqx]
    have hcoord_restrict (i : Fin (m + 1)) (j : Fin N) :
        Tendsto
          (fun ε => eLpNorm
            (fun x =>
              ((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have ht := hcoord_full i j
      rw [tendsto_order] at ht ⊢
      constructor
      · intro a ha
        exact (not_lt_of_ge bot_le ha).elim
      · intro b hb
        filter_upwards [ht.2 b hb] with ε hε
        exact lt_of_le_of_lt
          (MeasureTheory.eLpNorm_restrict_le
            (fun x =>
              ((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            ((m + 1 : ℕ) : ℝ≥0∞) volume K) hε
    have hcoord (i : Fin (m + 1)) (j : Fin N) :
        Tendsto
          (fun ε => eLpNorm
            (fun x => entry i j
              (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have heq : (fun ε => eLpNorm
            (fun x => entry i j
              (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K)) =ᶠ[
              nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun ε => eLpNorm
            (fun x =>
              ((standardMollifier ε) ⋆[
                ContinuousLinearMap.lsmul ℝ ℝ, volume] (q i j)) x - q i j x)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K)) := by
        filter_upwards [hsmall] with ε hε
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
        exact hscalar ε hε.1 hε.2 i j x hx
      exact (hcoord_restrict i j).congr' heq.symm
    have hpi {d : ℕ} (v : Fin d → ℝ) :
        ‖v‖ ≤ ∑ j, ‖v j‖ := by
      rw [Pi.norm_def]
      have hs := Finset.apply_sup_le_sum
        (f := fun r : ℝ≥0 => (r : ℝ))
        (by simp)
        (by
          intro a b
          change max (a : ℝ) (b : ℝ) ≤ (a : ℝ) + (b : ℝ)
          exact max_le_add_of_nonneg (NNReal.coe_nonneg a) (NNReal.coe_nonneg b))
        (s := fun j : Fin d => ‖v j‖₊)
        (Finset.univ : Finset (Fin d))
      simpa only [NNReal.coe_sum, coe_nnnorm] using hs
    have hcoord_le {d : ℕ} (v : Fin d → ℝ) (i : Fin d) :
        ‖v i‖ ≤ ‖v‖ := by
      rw [Pi.norm_def]
      exact_mod_cast Finset.le_sup (s := Finset.univ)
        (f := fun k : Fin d => ‖v k‖₊) (Finset.mem_univ i)
    have hOp (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) :
        ‖A‖ ≤ ∑ i, ∑ j, ‖entry i j A‖ := by
      apply A.opNorm_le_bound
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
      intro v
      have hvsum : (∑ i : Fin (m + 1), v i • (Pi.single i 1)) = v := by
        ext k
        simp [Pi.single_apply]
      calc
        ‖A v‖ = ‖A (∑ i : Fin (m + 1), v i • Pi.single i 1)‖ := by
          rw [hvsum]
        _ = ‖∑ i : Fin (m + 1), A (v i • Pi.single i 1)‖ := by
          rw [map_sum]
        _ ≤
            ∑ i : Fin (m + 1), ‖A (v i • Pi.single i 1)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ i : Fin (m + 1),
            ‖v‖ * (∑ j : Fin N, ‖entry i j A‖) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [map_smul, norm_smul]
          apply mul_le_mul (hcoord_le v i)
          · have hout := hpi (A (Pi.single i 1))
            change ‖A (Pi.single i 1)‖ ≤
              ∑ j : Fin N, ‖entry i j A‖
            exact hout
          · exact norm_nonneg _
          · exact norm_nonneg _
        _ = (∑ i : Fin (m + 1), ∑ j : Fin N, ‖entry i j A‖) * ‖v‖ := by
          rw [← Finset.mul_sum]
          exact mul_comm _ _
    have hmain_le (ε : ℝ) (hε : 0 < ε) :
        eLpNorm
            (fun x => fderiv ℝ (mollify ε f) x - fderiv ℝ f x)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) ≤
          ∑ i : Fin (m + 1), ∑ j : Fin N,
            eLpNorm
              (fun x => entry i j
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
              ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
      have hsmooth := mollify_contDiff hε hLip.continuous.locallyIntegrable
      have hDmeas : StronglyMeasurable
          (fun x => fderiv ℝ (mollify ε f) x - fderiv ℝ f x) :=
        ((hsmooth.continuous_fderiv (by simp)).measurable.sub
          (measurable_fderiv ℝ f)).stronglyMeasurable
      have hRmeas (z : Fin (m + 1) × Fin N) :
          AEStronglyMeasurable
            (fun x => ‖entry z.1 z.2
              (fderiv ℝ (mollify ε f) x - fderiv ℝ f x)‖)
            (volume.restrict K) := by
        exact ((((entry z.1 z.2).continuous.measurable.comp
          hDmeas.measurable).norm).stronglyMeasurable).aestronglyMeasurable
      calc
        eLpNorm
            (fun x => fderiv ℝ (mollify ε f) x - fderiv ℝ f x)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) ≤
          eLpNorm
            (fun x => ∑ i : Fin (m + 1), ∑ j : Fin N,
              ‖entry i j
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x)‖)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
              apply MeasureTheory.eLpNorm_mono_real
              intro x
              exact hOp _
        _ = eLpNorm
            (∑ z : Fin (m + 1) × Fin N, fun x =>
              ‖entry z.1 z.2
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x)‖)
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
              congr 1
              funext x
              simp only [Finset.sum_apply]
              rw [Fintype.sum_prod_type]
        _ ≤ ∑ z : Fin (m + 1) × Fin N,
            eLpNorm
              (fun x => ‖entry z.1 z.2
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x)‖)
              ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
              apply MeasureTheory.eLpNorm_sum_le
              · intro z hz
                exact hRmeas z
              · exact Fact.out
        _ = ∑ i : Fin (m + 1), ∑ j : Fin N,
            eLpNorm
              (fun x => entry i j
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
              ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
              rw [Fintype.sum_prod_type]
              simp only [eLpNorm_norm]
    have hsum_tendsto : Tendsto
        (fun ε => ∑ i : Fin (m + 1), ∑ j : Fin N,
          eLpNorm
            (fun x => entry i j
              (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
            ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hj (i : Fin (m + 1)) : Tendsto
          (fun ε => ∑ j : Fin N,
            eLpNorm
              (fun x => entry i j
                (fderiv ℝ (mollify ε f) x - fderiv ℝ f x))
              ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using tendsto_finsetSum Finset.univ
          (fun j hj => hcoord i j)
      simpa using tendsto_finsetSum Finset.univ (fun i hi => hj i)
    have ht := hsum_tendsto
    rw [tendsto_order] at ht ⊢
    constructor
    · intro a ha
      exact (not_lt_of_ge bot_le ha).elim
    · intro b hb
      filter_upwards [ht.2 b hb, hsmall] with ε hsum hε
      exact lt_of_le_of_lt (hmain_le ε hε.1) hsum
  · simpa only [Nat.cast_add, Nat.cast_one] using
      eventually_mollify_fderiv_memLpOn_compact hf hK

theorem lipschitz_fderiv_memLpOn_compact
    {m N : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {C : ℝ≥0} (hf : LipschitzWith C f)
    {K : Set ((Fin (m + 1) → ℝ))} (hK : IsCompact K) :
    MemLp (fun x => fderiv ℝ f x) (m + 1) (volume.restrict K) := by
  have hC := hf
  have hd : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x :=
    hC.ae_differentiableAt
  have hdr : ∀ᵐ x ∂volume.restrict K, DifferentiableAt ℝ f x :=
    ae_restrict_of_ae hd
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  apply MemLp.of_bound
    (measurable_fderiv ℝ f).stronglyMeasurable.aestronglyMeasurable C
  filter_upwards [hdr] with x hx
  exact norm_fderiv_le_of_lipschitz ℝ hC (x₀ := x)

end Mollification
end MathlibAnnex
