import MathlibAnnex.Analysis.Calculus.Piola
import MathlibAnnex.Analysis.Calculus.Mollification
import MathlibAnnex.Analysis.Normed.Operator.SelectedMinor
import MathlibAnnex.MeasureTheory.Integral.DeterminantContinuity

/-! # Integrals of maximal minors under compact perturbations -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal NNReal
namespace MathlibAnnex
namespace NullLagrangian
open Mollification

/-- A selected maximal minor of the derivative, using the fixed increasing row order. -/
def maximalMinorIntegrand {n N : ℕ} (s : Matrix.MaximalMinorIndex n (Fin N))
    (f : (Fin n → ℝ) → (Fin N → ℝ)) (x : Fin n → ℝ) : ℝ :=
  LinearMap.det ((ContinuousLinearMap.selectedSquare s (fderiv ℝ f x)).toLinearMap)

theorem selectedOutput_hasCompactSupport
    {n N : ℕ} (s : Matrix.MaximalMinorIndex n (Fin N)) {u : (Fin n → ℝ) → (Fin N → ℝ)}
    (huc : HasCompactSupport u) :
    HasCompactSupport (fun x => ContinuousLinearMap.selectedOutput s (u x)) :=
 by

  have hs : Function.support (fun x => ContinuousLinearMap.selectedOutput s (u x)) ⊆
      Function.support u := by
    intro x hx hux
    exact hx (by simp [hux])
  unfold HasCompactSupport at huc ⊢
  exact huc.of_isClosed_subset isClosed_closure (closure_mono hs)

theorem integral_maximalMinor_fderiv_add_sub_eq_zero_of_contDiff
    {m N : ℕ} (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {g u : (Fin (m + 1) → ℝ) → (Fin N → ℝ)}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (huc : HasCompactSupport u) :
    ∫ x, (maximalMinorIntegrand s (fun y => g y + u y) x -
      maximalMinorIntegrand s g x) = 0 :=
 by
  let π := ContinuousLinearMap.selectedOutput s
  have hgc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => π (g x)) := π.contDiff.comp hg
  have hucd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => π (u x)) := π.contDiff.comp hu
  have hucs : HasCompactSupport (fun x => π (u x)) :=
    selectedOutput_hasCompactSupport s huc
  have hsq := Piola.integral_det_fderiv_add_sub_eq_zero_of_contDiff hgc hucd hucs

  have hsum : (fun y => π (g y) + π (u y)) =
      (fun y => π (g y + u y)) := by
    funext y
    exact (map_add π (g y) (u y)).symm
  rw [hsum] at hsq
  have hplus : Differentiable ℝ (fun y => g y + u y) :=
    (hg.differentiable (by simp)).add (hu.differentiable (by simp))
  have hdplus : ∀ x, fderiv ℝ (fun y => π (g y + u y)) x =
      π.comp (fderiv ℝ (fun y => g y + u y) x) := by
    intro x
    exact (π.hasFDerivAt.comp x (hplus x).hasFDerivAt).fderiv
  have hdg : ∀ x, fderiv ℝ (fun y => π (g y)) x =
      π.comp (fderiv ℝ g x) := by
    intro x
    exact (π.hasFDerivAt.comp x
      ((hg.differentiable (by simp)) x).hasFDerivAt).fderiv
  simpa only [maximalMinorIntegrand, ContinuousLinearMap.selectedSquare, hdplus, hdg] using hsq
theorem maximalMinorIntegrand_mollify_continuous {n N : ℕ}
    (s : Matrix.MaximalMinorIndex n (Fin N)) {ε : ℝ} (hε : 0 < ε)
    {f : (Fin n → ℝ) → (Fin N → ℝ)} (hf : LocallyIntegrable f volume) :
    Continuous (maximalMinorIntegrand s (mollify ε f)) := by
  have hD : Continuous (fun x => fderiv ℝ (mollify ε f) x) :=
    (mollify_contDiff hε hf).continuous_fderiv (by simp)
  change Continuous (fun x => LinearMap.det ((ContinuousLinearMap.selectedSquare s
    (fderiv ℝ (mollify ε f) x)).toLinearMap))
  apply ContinuousLinearMap.continuous_det.comp
  convert (ContinuousLinearMap.selectedSquareCLM s).continuous.comp hD using 1
  funext x
  exact ContinuousLinearMap.selectedSquareCLM_apply s _


theorem tendsto_integral_maximalMinor_mollify
    {m N : ℕ} (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {f : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {K : Set (Fin (m + 1) → ℝ)} (hK : IsCompact K) :
    Tendsto (fun ε => ∫ x in K, maximalMinorIntegrand s (mollify ε f) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in K, maximalMinorIntegrand s f x)) := by
  have hstrong := tendsto_eLpNorm_fderiv_mollify_sub hf hK
  have hQ := lipschitz_fderiv_memLpOn_compact hf hK
  apply MathlibAnnex.MeasureTheory.tendsto_integral_det_of_strongLn (Nat.succ_pos m)
  · constructor
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong.1
      · intro ε; exact bot_le
      · intro ε
        apply eLpNorm_mono
        intro x
        rw [← ContinuousLinearMap.selectedSquare_sub]
        exact ContinuousLinearMap.norm_selectedSquare_le s _
    · filter_upwards [hstrong.2] with ε hε
      simpa only [ContinuousLinearMap.selectedSquareCLM_apply] using
        hε.continuousLinearMap_comp (ContinuousLinearMap.selectedSquareCLM s)
  · simpa only [ContinuousLinearMap.selectedSquareCLM_apply, Nat.cast_add, Nat.cast_one,
      Nat.cast_succ] using
      hQ.continuousLinearMap_comp (ContinuousLinearMap.selectedSquareCLM s)

theorem integrableOn_maximalMinor_fderiv_of_lipschitzWith
    {m N : ℕ} (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {f : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {K : Set (Fin (m + 1) → ℝ)} (hK : IsCompact K) :
    IntegrableOn (maximalMinorIntegrand s f) K := by
  let Q := fun x => ContinuousLinearMap.selectedSquare s (fderiv ℝ f x)
  have hQ : MemLp Q ((m + 1 : ℕ) : ℝ≥0∞) (volume.restrict K) := by
    simpa only [Q, ContinuousLinearMap.selectedSquareCLM_apply, Nat.cast_add, Nat.cast_one] using
      (lipschitz_fderiv_memLpOn_compact hf hK).continuousLinearMap_comp
        (ContinuousLinearMap.selectedSquareCLM s)
  have hzero : LinearMap.det (0 : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) = 0 := by
    rw [← LinearMap.det_toMatrix']
    simpa using (Matrix.det_zero (inferInstance : Nonempty (Fin (m + 1))))
  have hb : ∀ x, ‖LinearMap.det (Q x).toLinearMap‖ ≤ (m + 1 : ℕ) * ‖Q x‖ ^ (m + 1) := by
    intro x
    have h := MathlibAnnex.ContinuousLinearMap.norm_det_sub_le (Q x) 0
    simpa [hzero, pow_succ, mul_assoc] using h
  exact ((hQ.integrable_norm_pow (Nat.succ_ne_zero m)).const_mul (m + 1 : ℕ)).mono'
    (ContinuousLinearMap.continuous_det.comp_aestronglyMeasurable hQ.1)
    (ae_of_all _ hb)

theorem topMinor_difference_eq_zero_of_not_mem_tsupport
    {n N : ℕ} (s : Matrix.MaximalMinorIndex n (Fin N))
    {g u : (Fin n → ℝ) → (Fin N → ℝ)}
    {x : (Fin n → ℝ)} (hx : x ∉ tsupport u) :
    maximalMinorIntegrand s (fun y => g y + u y) x -
      maximalMinorIntegrand s g x = 0 := by
  have hu0 : u =ᶠ[nhds x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hsum : (fun y => g y + u y) =ᶠ[nhds x] g := by
    filter_upwards [hu0] with y hy
    simp [hy]
  have hfd : fderiv ℝ (fun y => g y + u y) x = fderiv ℝ g x :=
    hsum.fderiv_eq
  simp [maximalMinorIntegrand, hfd]

theorem integral_topMinor_difference_eq_setIntegral
    {n N : ℕ} (s : Matrix.MaximalMinorIndex n (Fin N)) {K : Set ((Fin n → ℝ))}
    {g u : (Fin n → ℝ) → (Fin N → ℝ)}
    (hsupp : tsupport u ⊆ K) :
    ∫ x, (maximalMinorIntegrand s (fun y => g y + u y) x -
      maximalMinorIntegrand s g x) =
      ∫ x in K, (maximalMinorIntegrand s (fun y => g y + u y) x -
        maximalMinorIntegrand s g x) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hxK
  exact topMinor_difference_eq_zero_of_not_mem_tsupport s
    (fun hxu => hxK (hsupp hxu))
theorem integral_maximalMinor_fderiv_add_sub_eq_zero_of_lipschitzWith
    {m N : ℕ} (s : Matrix.MaximalMinorIndex (m + 1) (Fin N))
    {g u : (Fin (m + 1) → ℝ) → (Fin N → ℝ)}
    {Cg Cu : ℝ≥0} (hg : LipschitzWith Cg g) (hu : LipschitzWith Cu u) (huc : HasCompactSupport u) :
    ∫ x, (maximalMinorIntegrand s (fun y => g y + u y) x -
      maximalMinorIntegrand s g x) = 0 := by

  have hgW := hg
  have huW := hu
  have hgL := hgW
  have huL := huW
  have hgLI : LocallyIntegrable g volume := hgW.continuous.locallyIntegrable
  have huLI : LocallyIntegrable u volume := huW.continuous.locallyIntegrable
  rcases eventually_tsupport_mollify_subset_compact huc with
    ⟨K, hK, hsupp_u, hKsupp⟩
  have hplus : LipschitzWith (Cg + Cu) (fun x => g x + u x) := hgW.add huW
  have hsmooth : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ x in K, (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
        maximalMinorIntegrand s (mollify ε g) x) = 0 := by
    filter_upwards [hKsupp, self_mem_nhdsWithin] with ε hsupp hε
    have hε' : 0 < ε := hε
    rw [mollify_add ε g u hgLI huLI]
    rw [← integral_topMinor_difference_eq_setIntegral s hsupp]
    exact integral_maximalMinor_fderiv_add_sub_eq_zero_of_contDiff s
      (mollify_contDiff hε' hgLI)
      (mollify_contDiff hε' huLI)
      (hK.of_isClosed_subset (isClosed_tsupport _) hsupp)
  have hconv_plus := tendsto_integral_maximalMinor_mollify s hplus hK
  have hconv_g := tendsto_integral_maximalMinor_mollify s hgL hK
  have hsplit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ x in K,
        (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
          maximalMinorIntegrand s (mollify ε g) x)) =
        (∫ x in K, maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x) -
          ∫ x in K, maximalMinorIntegrand s (mollify ε g) x := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    exact MeasureTheory.integral_sub
      (ContinuousOn.integrableOn_compact hK
        (maximalMinorIntegrand_mollify_continuous s hε'
        (hplus.continuous.locallyIntegrable)).continuousOn)
      (ContinuousOn.integrableOn_compact hK
        (maximalMinorIntegrand_mollify_continuous s hε' hgLI).continuousOn)
  have hdiff : Tendsto
      (fun ε => ∫ x in K,
        (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
          maximalMinorIntegrand s (mollify ε g) x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in K,
        (maximalMinorIntegrand s (fun y => g y + u y) x -
          maximalMinorIntegrand s g x))) := by
    have hplusInt := integrableOn_maximalMinor_fderiv_of_lipschitzWith s hplus hK
    have hgInt := integrableOn_maximalMinor_fderiv_of_lipschitzWith s hgL hK
    have hlimit :
        (∫ x in K,
          (maximalMinorIntegrand s (fun y => g y + u y) x -
            maximalMinorIntegrand s g x)) =
          (∫ x in K, maximalMinorIntegrand s (fun y => g y + u y) x) -
            ∫ x in K, maximalMinorIntegrand s g x :=
      MeasureTheory.integral_sub hplusInt hgInt
    rw [hlimit]
    have hsplitEq :
        (fun ε =>
          (∫ x in K,
            (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
              maximalMinorIntegrand s (mollify ε g) x))) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun ε =>
            (∫ x in K, maximalMinorIntegrand s
              (mollify ε (fun y => g y + u y)) x) -
              ∫ x in K, maximalMinorIntegrand s (mollify ε g) x) := hsplit
    exact (hconv_plus.sub hconv_g).congr' hsplitEq.symm
  have hzero : ∫ x in K,
      (maximalMinorIntegrand s (fun y => g y + u y) x -
        maximalMinorIntegrand s g x) = 0 := by
    have heq :
        (fun ε => ∫ x in K,
          (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
            maximalMinorIntegrand s (mollify ε g) x)) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun _ => 0) := hsmooth
    have hzlim : Tendsto
        (fun ε => ∫ x in K,
          (maximalMinorIntegrand s (mollify ε (fun y => g y + u y)) x -
            maximalMinorIntegrand s (mollify ε g) x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' heq.symm
    exact tendsto_nhds_unique hdiff hzlim
  rw [integral_topMinor_difference_eq_setIntegral s hsupp_u]
  exact hzero


end NullLagrangian
end MathlibAnnex
