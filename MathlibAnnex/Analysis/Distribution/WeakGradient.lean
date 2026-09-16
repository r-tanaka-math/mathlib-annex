import MathlibAnnex.Analysis.Distribution.WeakGradient.Local

/-! Weak-gradient-zero rigidity on a finite-dimensional real normed space.
No choice of coordinates, positive dimension, bounded domain, or global
integrability assumption occurs in the conclusion.  The parent RET2 source
was independently elaborated; this API-repair revision is qualified by the exact build evidence accompanying this source. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace MathlibAnnex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Local conclusion on any open domain; no connectedness is needed. -/
theorem WeakDivergenceZero.locally_aeConstant
    {U : Set E} {u : E → ℝ} (hweak : WeakDivergenceZero μ U u)
    (hU : IsOpen U) (hu : LocallyIntegrableOn u U μ)
    {x : E} (hx : x ∈ U) : Nonempty (LocalAEConstantAt μ U u x) :=
  WeakGradient.exists_localAEConstantAt hU hu hweak hx

/-- Global a.e. constancy, including the empty-domain and zero-dimensional cases. -/
theorem WeakDivergenceZero.exists_aeConstantOn
    {U : Set E} {u : E → ℝ} (hweak : WeakDivergenceZero μ U u)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : LocallyIntegrableOn u U μ) :
    ∃ c : ℝ, AEConstantOn μ u U c := by
  exact exists_aeConstantOn_of_local_preconnected μ hUc
    (HereditarilyLindelofSpace.isLindelof U)
    (fun _ hx => hweak.locally_aeConstant hU hu hx)

/-- Continuity is the extra hypothesis needed to upgrade the a.e. statement. -/
theorem WeakDivergenceZero.exists_eqOn
    {U : Set E} {u : E → ℝ} (hweak : WeakDivergenceZero μ U u)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hu : LocallyIntegrableOn u U μ)
    (hcont : ContinuousOn u U) : ∃ c : ℝ, Set.EqOn u (fun _ => c) U := by
  rcases hweak.exists_aeConstantOn hU hUc hu with ⟨c, hc⟩
  exact ⟨c, Measure.eqOn_open_of_ae_eq hc hU hcont continuousOn_const⟩

end MathlibAnnex
