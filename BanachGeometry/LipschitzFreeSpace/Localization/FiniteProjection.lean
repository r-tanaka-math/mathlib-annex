/- R6 8.1: weak convergence implies norm convergence after a finite-dimensional projection.
New proof body over the fixed Mathlib finite-basis continuous-equivalence API.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.LipschitzFreeSpace.Localization.IncrementCondition
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped Topology
open Filter
namespace BanachGeometry.LipschitzFreeLocalization

/-- All finite-dimensional real Banach spaces have the sequence Schur property.
The empty basis (dimension zero) is included without a nontriviality assumption. -/
theorem tendsto_zero_of_weakNull_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u : ℕ → E} (hu : BanachGeometry.WeakNull u) : Tendsto u atTop (𝓝 0) := by
  let e := (Module.finBasis ℝ E).equivFunL
  have ht : Tendsto (fun n => e (u n)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact hu ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)
  have hi := (e.symm.continuous.tendsto 0).comp ht
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, map_zero] using hi

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The finite-dimensional head term used in the general increment argument. -/
theorem tendsto_norm_starProjection_zero (F : Submodule ℝ H) [FiniteDimensional ℝ F]
    [F.HasOrthogonalProjection] {b : ℕ → H} (hb : BanachGeometry.WeakNull b) :
    Tendsto (fun n => ‖F.starProjection (b n)‖) atTop (𝓝 0) := by
  have hw : BanachGeometry.WeakNull (fun n => F.orthogonalProjectionOnto (b n)) := by
    intro f
    exact hb (f.comp F.orthogonalProjectionOnto)
  have ht := (tendsto_zero_of_weakNull_finiteDimensional hw).norm
  change Tendsto (fun n => ‖F.orthogonalProjectionOnto (b n)‖) atTop (𝓝 0)
  simpa only [norm_zero] using ht

end BanachGeometry.LipschitzFreeLocalization
