import MathlibAnnex.Analysis.Calculus.BilipschitzOrientation.Piola
import MathlibAnnex.Analysis.Distribution.WeakGradient
import Mathlib.Tactic

/-!
# Degree-free orientation for global bi-Lipschitz data: constancy and volume

Target preconnectedness, positive measure, and finite measure are separated at
the exact steps where they are used:

* preconnectedness glues local a.e. constants;
* positive measure forces the constant sign to be `+1` or `-1`;
* finite measure evaluates the integral of the constant.

No assertion of one global sign is made on an arbitrary disconnected target.
This browser-produced source is `HANDWRITTEN_UNBUILT` until local elaboration.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal

namespace MathlibAnnex
namespace BilipschitzOrientation

/-- The transported sign is locally integrable because it is measurable and
bounded in norm by one. -/
theorem targetJacobianSign_locallyIntegrableOn {n : ℕ}
    (D : BiLipschitzOpenData n) :
    LocallyIntegrableOn (targetJacobianSign D) D.target := by
  have hfderiv_meas : Measurable
      (fun x : Fin n → ℝ => fderiv ℝ D.f x) := measurable_fderiv ℝ D.f
  have hdet_meas : Measurable
      (fun x : Fin n → ℝ => (fderiv ℝ D.f x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp hfderiv_meas
  have hdomain_meas : Measurable (domainJacobianSign D) := by
    unfold domainJacobianSign
    exact Measurable.ite
      (measurableSet_Ici.preimage hdet_meas)
      measurable_const measurable_const
  have htarget_meas : Measurable (targetJacobianSign D) := by
    exact hdomain_meas.comp D.lipschitzWith_g.continuous.measurable
  refine (locallyIntegrableOn_const (μ := volume)
      (s := D.target) (1 : ℝ)).mono
    htarget_meas.aestronglyMeasurable ?_
  filter_upwards with y
  simp

/-- On a preconnected open target, the transported Jacobian sign is a.e.
constant.  This is the exact R05 weak-divergence-zero interface. -/
theorem targetJacobianSign_ae_const {n : ℕ}
    (D : BiLipschitzOpenData n) (hpre : IsPreconnected D.target) :
    ∃ c : ℝ, AEConstantOn volume (targetJacobianSign D) D.target c := by
  exact (targetJacobianSign_weakDivergenceZero D).exists_aeConstantOn
    D.target_open hpre (targetJacobianSign_locallyIntegrableOn D)

/-- Positive target measure excludes a vacuous a.e. constant and forces its
value to be exactly `+1` or `-1`. -/
theorem targetJacobianSign_const_is_pm_one {n : ℕ}
    (D : BiLipschitzOpenData n) {c : ℝ}
    (hc : AEConstantOn volume (targetJacobianSign D) D.target c)
    (hpos : 0 < volume D.target) : c = 1 ∨ c = -1 := by
  change ∀ᵐ y ∂volume.restrict D.target, targetJacobianSign D y = c at hc
  obtain ⟨y, hyT, hyc⟩ :=
    MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := volume) (s := D.target) (ne_of_gt hpos) hc
  have habs : |c| = 1 := by
    simpa [hyc] using abs_targetJacobianSign D y
  exact eq_or_eq_neg_of_abs_eq habs

/-- The total signed Jacobian integral is one real orientation sign times the
finite target volume.  The sign is returned as a real number with an explicit
`±1` certificate, rather than duplicating the SR-specific Plücker sign type. -/
theorem integral_det_fderiv_eq_signed_volume {n : ℕ}
    (D : BiLipschitzOpenData n) (hpre : IsPreconnected D.target)
    (hpos : 0 < volume D.target) (hfinite : volume D.target ≠ ∞) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∫ x in D.source, (fderiv ℝ D.f x).det ∂volume =
        ε * (volume D.target).toReal := by
  obtain ⟨c, hc⟩ := targetJacobianSign_ae_const D hpre
  have hpm : c = 1 ∨ c = -1 :=
    targetJacobianSign_const_is_pm_one D hc hpos
  refine ⟨c, hpm, ?_⟩
  have htransfer := signed_area_transfer D
    (φ := fun _ => (1 : ℝ)) (by
      simpa using integrableOn_const (μ := volume) (C := (1 : ℝ)) hfinite)
  change ∀ᵐ y ∂volume.restrict D.target, targetJacobianSign D y = c at hc
  calc
    ∫ x in D.source, (fderiv ℝ D.f x).det ∂volume =
        ∫ y in D.target, targetJacobianSign D y ∂volume := by
      simpa using htransfer
    _ = ∫ y in D.target, c ∂volume := integral_congr_ae hc
    _ = c * (volume D.target).toReal := by
      rw [MeasureTheory.setIntegral_const]
      change (volume D.target).toReal * c = c * (volume D.target).toReal
      exact mul_comm _ _

end BilipschitzOrientation
end MathlibAnnex
