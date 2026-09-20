import MathlibAnnex.Analysis.Normed.Plucker.RecoveryCertificate
import MathlibAnnex.Analysis.Normed.Ball.VolumeRigidity
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compact recovery limit, exact top volume, and rigidity of the ball image. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ENNReal
namespace MathlibAnnex.PluckerRecovery
namespace Internal
private abbrev clmMatrix {n N : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) := LinearMap.toMatrix' A.toLinearMap
private def recoveryEpsilon (k : ℕ) : ℝ := 1 / ((k + 2 : ℕ) : ℝ)

@[simp] private theorem recoveryEpsilon_pos (k : ℕ) : 0 < recoveryEpsilon k := by
  -- [R11-API-CHECK:LIM-001]
  apply one_div_pos.mpr
  exact_mod_cast (by omega : 0 < k + 2)

@[simp] private theorem recoveryEpsilon_le_half (k : ℕ) :
    recoveryEpsilon k ≤ (1 / 2 : ℝ) := by
  -- [R11-API-CHECK:LIM-002]
  have hden : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ k + 2)
  exact one_div_le_one_div_of_le (by norm_num) hden

/-- The chosen distortions converge to zero. -/
private theorem tendsto_recoveryEpsilon_zero :
    Filter.Tendsto recoveryEpsilon Filter.atTop (nhds 0) := by
  -- [R11-API-CHECK:LIM-003]
  change Filter.Tendsto (fun k : ℕ => 1 / (((k + 2 : ℕ) : ℝ)))
    Filter.atTop (nhds 0)
  have hden : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 2)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 2
      tendsto_natCast_atTop_atTop
  simpa only [one_div, Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_inv_atTop_zero.comp hden)

/-- Choice of one recovery certificate at each canonical distortion. -/
private noncomputable def recoveryCertificateSequence {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) : LinearCertificate MX MY (recoveryEpsilon k) :=
  Classical.choice
    (nonempty_linearCertificate_of_pluckerBodies_eq MX MY
      (recoveryEpsilon_pos k) hBodies)

/-- The square map in the `k`-th recovery certificate. -/
private noncomputable def recoveryMapSequence {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  (recoveryCertificateSequence MX MY hBodies k).linearMap

/-- Uniform reference-norm bound for the whole recovery sequence. -/
private theorem recoveryMapSequence_referenceNorm_le {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) (x : (Fin (m + 1) → ℝ)) :
    ‖recoveryMapSequence MX MY hBodies k x‖ ≤
      (2 * MX.upper / MY.lower) * ‖x‖ := by
  -- [R11-API-CHECK:LIM-004]
  exact (recoveryCertificateSequence MX MY hBodies k).referenceNorm_le
    (recoveryEpsilon_le_half k) x

/-- Exact top-volume identity for every map in the sequence. -/
private theorem closedUnitBallVolume_mul_abs_det_recoveryMapSequence {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) :
    MX.closedUnitBallVolume *
        |Matrix.det (clmMatrix (recoveryMapSequence MX MY hBodies k))| =
      MY.closedUnitBallVolume := by
  -- [R11-API-CHECK:LIM-005]
  let C := recoveryCertificateSequence MX MY hBodies k
  have h := C.closedUnitBallVolume_mul_abs_det
  rw [C.det_eq] at h
  simpa [recoveryMapSequence, C] using h

/-- Vanishing-distortion model estimate for every sequence term. -/
private theorem one_sub_mul_seminorm_recoveryMapSequence_le {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) (x : (Fin (m + 1) → ℝ)) :
    (1 - recoveryEpsilon k) *
        MY.p (recoveryMapSequence MX MY hBodies k x) ≤ MX.p x := by
  exact (recoveryCertificateSequence MX MY hBodies k).one_sub_mul_seminorm_linearMap_le x
private def recoveryOperatorRadius {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) : ℝ :=
  2 * MX.upper / MY.lower

@[simp] private theorem recoveryOperatorRadius_pos {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    0 < recoveryOperatorRadius MX MY := by
  unfold recoveryOperatorRadius
  exact div_pos (mul_pos (by norm_num) MX.upper_pos) MY.lower_pos

@[simp] private theorem recoveryOperatorRadius_nonneg {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    0 ≤ recoveryOperatorRadius MX MY :=
  (recoveryOperatorRadius_pos MX MY).le

/-- One closed operator ball containing every recovery map. -/
private def recoveryOperatorCarrier {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    Set ((Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)) :=
  Metric.closedBall 0 (recoveryOperatorRadius MX MY)

/-- Each canonical recovery map lies in the common carrier. -/
private theorem recoveryMapSequence_mem_carrier {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N)
    (k : ℕ) :
    recoveryMapSequence MX MY hBodies k ∈
      recoveryOperatorCarrier MX MY := by
  -- [R11-API-CHECK:LIM-101]
  have hop : ‖recoveryMapSequence MX MY hBodies k‖ ≤
      recoveryOperatorRadius MX MY := by
    exact (recoveryMapSequence MX MY hBodies k).opNorm_le_bound
      (recoveryOperatorRadius_nonneg MX MY)
      (recoveryMapSequence_referenceNorm_le MX MY hBodies k)
  simpa [recoveryOperatorCarrier, Metric.mem_closedBall, dist_eq_norm,
    recoveryOperatorRadius] using hop

/-- The common operator carrier is compact. -/
private theorem isCompact_recoveryOperatorCarrier {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) :
    IsCompact (recoveryOperatorCarrier MX MY) := by
  -- [R11-API-CHECK:LIM-102]
  exact Metric.isCompact_of_isClosed_isBounded
    Metric.isClosed_closedBall Metric.isBounded_closedBall

/-- A chosen convergent subsequence of the recovery maps. -/
private structure RecoverySubsequence {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) where
  limit : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)
  index : ℕ → ℕ
  strictMono : StrictMono index
  tendsto : Tendsto
    (fun j => recoveryMapSequence MX MY hBodies (index j))
    atTop (nhds limit)
  limit_mem : limit ∈ recoveryOperatorCarrier MX MY

/-- Compactness supplies a convergent subsequence. -/
private theorem nonempty_recoverySubsequence {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (RecoverySubsequence MX MY hBodies) := by
  -- [R11-API-CHECK:LIM-103]
  rcases (isCompact_recoveryOperatorCarrier MX MY).tendsto_subseq
      (fun k => recoveryMapSequence_mem_carrier MX MY hBodies k) with
    ⟨L, hL, φ, hφ, hconv⟩
  exact ⟨{
    limit := L
    index := φ
    strictMono := hφ
    tendsto := by simpa [Function.comp_def] using hconv
    limit_mem := hL
  }⟩
private theorem tendsto_clm_apply {n : ℕ}
    {A : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    {L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hA : Tendsto A atTop (nhds L)) (x : (Fin n → ℝ)) :
    Tendsto (fun k => A k x) atTop (nhds (L x)) := by
  -- [R11-API-CHECK:LIM-201]
  exact (((ContinuousLinearMap.apply ℝ ((Fin n → ℝ))) x).continuous.continuousAt.tendsto.comp hA)

namespace RecoverySubsequence

variable {m : ℕ} {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    {hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N}
    (S : RecoverySubsequence MX MY hBodies)

/-- The distortions along the strict subsequence still tend to zero. -/
private theorem tendsto_epsilon_zero :
    Tendsto (fun j => recoveryEpsilon (S.index j)) atTop (nhds 0) := by
  -- [R11-API-CHECK:LIM-202]
  exact tendsto_recoveryEpsilon_zero.comp S.strictMono.tendsto_atTop

/-- The selected maps converge pointwise. -/
private theorem tendsto_apply (x : (Fin (m + 1) → ℝ)) :
    Tendsto
      (fun j => recoveryMapSequence MX MY hBodies (S.index j) x)
      atTop (nhds (S.limit x)) :=
  tendsto_clm_apply S.tendsto x

/-- Exact model contraction inequality for the limit map. -/
private theorem seminorm_limit_le (x : (Fin (m + 1) → ℝ)) :
    MY.p (S.limit x) ≤ MX.p x := by
  -- [R11-API-CHECK:LIM-203]
  have hε := S.tendsto_epsilon_zero
  have hpx : Tendsto
      (fun j => MY.p
        (recoveryMapSequence MX MY hBodies (S.index j) x))
      atTop (nhds (MY.p (S.limit x))) :=
    MY.continuous_p.continuousAt.tendsto.comp (S.tendsto_apply x)
  have hleft : Tendsto
      (fun j => (1 - recoveryEpsilon (S.index j)) *
        MY.p (recoveryMapSequence MX MY hBodies (S.index j) x))
      atTop (nhds (MY.p (S.limit x))) := by
    convert ((tendsto_const_nhds.sub hε).mul hpx) using 1; ring
  have hev : ∀ᶠ j in atTop,
      (1 - recoveryEpsilon (S.index j)) *
        MY.p (recoveryMapSequence MX MY hBodies (S.index j) x) ≤
      MX.p x :=
    Filter.Eventually.of_forall fun j =>
      one_sub_mul_seminorm_recoveryMapSequence_le MX MY hBodies (S.index j) x
  exact le_of_tendsto hleft hev

/-- The limit sends the source model unit ball into the target model unit ball. -/
private theorem limit_image_unitBall_subset :
    S.limit '' MX.closedUnitBall ⊆ MY.closedUnitBall := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact MY.mem_closedUnitBall.mpr
    ((S.seminorm_limit_le x).trans (MX.mem_closedUnitBall.mp hx))

end RecoverySubsequence
namespace RecoverySubsequence

variable {m : ℕ} {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    {hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N}
    (S : RecoverySubsequence MX MY hBodies)

/-- Determinants of the selected maps converge to the determinant of the limit. -/
private theorem tendsto_coordDet :
    Tendsto
      (fun j => ContinuousLinearMap.det
        (recoveryMapSequence MX MY hBodies (S.index j)))
      atTop (nhds (ContinuousLinearMap.det S.limit)) := by
  exact ContinuousLinearMap.continuous_det.continuousAt.tendsto.comp S.tendsto

/-- The exact top-volume identity passes to the limit. -/
private theorem closedUnitBallVolume_mul_abs_det_limit :
    MX.closedUnitBallVolume * |ContinuousLinearMap.det S.limit| = MY.closedUnitBallVolume := by
  -- [R11-API-CHECK:LIM-301]
  have hcont : Continuous
      (fun A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) =>
        MX.closedUnitBallVolume * |ContinuousLinearMap.det A|) :=
    continuous_const.mul ContinuousLinearMap.continuous_det.abs
  have h₁ : Tendsto
      (fun j => MX.closedUnitBallVolume *
        |ContinuousLinearMap.det (recoveryMapSequence MX MY hBodies (S.index j))|)
      atTop (nhds (MX.closedUnitBallVolume * |ContinuousLinearMap.det S.limit|)) :=
    hcont.continuousAt.tendsto.comp S.tendsto
  have hterm : ∀ j,
      MX.closedUnitBallVolume *
        |ContinuousLinearMap.det (recoveryMapSequence MX MY hBodies (S.index j))| =
      MY.closedUnitBallVolume := by
    intro j
    simpa [ContinuousLinearMap.det] using
      closedUnitBallVolume_mul_abs_det_recoveryMapSequence MX MY hBodies (S.index j)
  have hfun :
      (fun j => MX.closedUnitBallVolume *
        |ContinuousLinearMap.det (recoveryMapSequence MX MY hBodies (S.index j))|) =
      (fun _ : ℕ => MY.closedUnitBallVolume) := funext hterm
  have h₂ : Tendsto
      (fun j => MX.closedUnitBallVolume *
        |ContinuousLinearMap.det (recoveryMapSequence MX MY hBodies (S.index j))|)
      atTop (nhds MY.closedUnitBallVolume) := by
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h₁ h₂

/-- The limit determinant cannot vanish. -/
private theorem limit_coordDet_ne_zero : ContinuousLinearMap.det S.limit ≠ 0 := by
  intro hzero
  have hvol := S.closedUnitBallVolume_mul_abs_det_limit
  rw [hzero, abs_zero, mul_zero] at hvol
  exact MY.closedUnitBallVolume_pos.ne' hvol.symm

/-- The compact limit is injective. -/
private theorem limit_injective : Function.Injective S.limit :=
  by
  apply LinearMap.ker_eq_bot.mp
  exact not_not.mp ((LinearMap.det_eq_zero_iff_ker_ne_bot).not.mp S.limit_coordDet_ne_zero)

/-- The compact limit is surjective. -/
private theorem limit_surjective : Function.Surjective S.limit :=
  (LinearMap.injective_iff_surjective).mp S.limit_injective

end RecoverySubsequence

end Internal
open Internal
structure LimitCertificate {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)) where
  linearMap : (Fin (m + 1) → ℝ) →linearMap[ℝ] (Fin (m + 1) → ℝ)
  seminorm_linearMap_le : ∀ x, MY.p (linearMap x) ≤ MX.p x
  image_closedUnitBall_subset : linearMap '' MX.closedUnitBall ⊆ MY.closedUnitBall
  closedUnitBallVolume_mul_abs_det : MX.closedUnitBallVolume * |ContinuousLinearMap.det linearMap| = MY.closedUnitBallVolume
  det_ne_zero : ContinuousLinearMap.det linearMap ≠ 0
  injective : Function.Injective linearMap
  surjective : Function.Surjective linearMap

/-- Equality of all finite Plücker bodies yields a limit recovery certificate. -/
theorem nonempty_limitCertificate_of_pluckerBodies_eq {m : ℕ}
    (MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ))
    (hBodies : ∀ N : ℕ, PluckerBody.body MX N = PluckerBody.body MY N) :
    Nonempty (LimitCertificate MX MY) := by
  let S := Classical.choice (nonempty_recoverySubsequence MX MY hBodies)
  exact ⟨{
    linearMap := S.limit
    seminorm_linearMap_le := S.seminorm_limit_le
    image_closedUnitBall_subset := S.limit_image_unitBall_subset
    closedUnitBallVolume_mul_abs_det := S.closedUnitBallVolume_mul_abs_det_limit
    det_ne_zero := S.limit_coordDet_ne_zero
    injective := S.limit_injective
    surjective := S.limit_surjective
  }⟩

namespace Internal
private noncomputable def linearImageBallVolume {n : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : ℝ :=
  (volume (A '' M.closedUnitBall)).toReal

/-- The real-valued image volume is `|det A|` times the source ball volume. -/
private theorem linearImageBallVolume_eq {n : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ)) (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    linearImageBallVolume M A = |ContinuousLinearMap.det A| * M.closedUnitBallVolume := by
  -- [R11-API-CHECK:LIMVOL-002]
  rw [linearImageBallVolume, MeasureTheory.Measure.addHaar_image_continuousLinearMap,
    ENNReal.toReal_mul]
  simp [EquivalentSeminorm.closedUnitBallVolume, abs_nonneg]

/-- Equality of finite ENNReal values follows from equality of their real parts. -/
private theorem ennreal_eq_of_toReal_eq {a b : ℝ≥0∞}
    (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h : a.toReal = b.toReal) :
    a = b := by
  -- [R11-API-CHECK:LIMVOL-003]
  apply le_antisymm
  · exact (ENNReal.toReal_le_toReal ha hb).mp h.le
  · exact (ENNReal.toReal_le_toReal hb ha).mp h.ge

namespace LimitRecoveryCertificate
variable {m : ℕ} {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)} (C : LimitCertificate MX MY)
private theorem linearImageBallVolume_eq_target :
    linearImageBallVolume MX C.linearMap = MY.closedUnitBallVolume := by
  rw [linearImageBallVolume_eq]
  simpa [mul_comm] using C.closedUnitBallVolume_mul_abs_det

end LimitRecoveryCertificate
end Internal

namespace LimitCertificate
variable {m : ℕ} {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)} (C : LimitCertificate MX MY)
theorem measure_image_unitBall_eq :
    volume (C.linearMap '' MX.closedUnitBall) = volume MY.closedUnitBall := by
  -- [R11-API-CHECK:LIMVOL-004]
  apply ennreal_eq_of_toReal_eq
  · exact (MX.closedUnitBall_isCompact.image C.L.continuous).measure_ne_top
  · exact MY.closedUnitBall_isCompact.measure_ne_top
  · simpa [linearImageBallVolume, EquivalentSeminorm.closedUnitBallVolume] using
      Internal.LimitRecoveryCertificate.linearImageBallVolume_eq_target C

/-- Inclusion and exact measure force equality: strict containment loses measure. -/
theorem image_unitBall_eq : C.linearMap '' MX.closedUnitBall = MY.closedUnitBall := by
  by_contra hne
  have hlt : volume (C.linearMap '' MX.closedUnitBall) < volume MY.closedUnitBall :=
    SeminormBall.measure_lt volume MY.p MY.continuous_p
      (MX.closedUnitBall_isCompact.image C.L.continuous) C.image_closedUnitBall_subset hne
  exact hlt.ne C.measure_image_unitBall_eq
end LimitCertificate
end MathlibAnnex.PluckerRecovery
