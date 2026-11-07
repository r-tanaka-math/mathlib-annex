import BanachGeometry.NoC0.BPFiniteLower

/-! BP-basis: no linear c₀ copy implies norm decay of images of its basis.
Finite-dimensional norming, annihilating functionals and triangular
selection are proved in the imported sources. No WSC, separability,
completeness, unconditional convergence axiom, or free-space restriction.
Local execution evidence is recorded in the external qualification receipts;
Annex, hosted and release status are recorded separately. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace BP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem containsLinearCopy_of_not_tendsto_norm_image_scalarBasis (T : ScalarC0 →L[ℝ] E)
    (hnot : ¬ Tendsto (fun n => ‖T (CanonicalSequences.scalarBasis n)‖) atTop (nhds 0)) :
    ContainsLinearCopy ScalarC0 E := by
  classical
  have hbad : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ k, N ≤ k ∧ δ ≤ ‖T (CanonicalSequences.scalarBasis k)‖ := by
    by_contra! h
    apply hnot
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,?_⟩
    intro n hn
    simpa only [dist_zero_right,Real.norm_of_nonneg (norm_nonneg _)] using hN n hn
  obtain ⟨δ,hδ,hbad⟩ := hbad
  let u := fun k => T (CanonicalSequences.scalarBasis k)
  let d := triangularData u (BasisSeries.weakNull_image_basis T) δ hδ hbad
  let J := T.comp (insertCLM d.k)
  refine ⟨J,δ/8,by positivity,?_⟩
  intro a
  have hleft : Tendsto (fun N => (δ/8)*‖CanonicalSequences.scalarHead N a‖)
      atTop (nhds ((δ/8)*‖a‖)) :=
    (CanonicalSequences.tendsto_scalarHead a).norm.const_mul (δ/8)
  have hright : Tendsto (fun N => ‖J (CanonicalSequences.scalarHead N a)‖)
      atTop (nhds ‖J a‖) :=
    ((J.continuous.tendsto a).comp (CanonicalSequences.tendsto_scalarHead a)).norm
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall (fun N => mul_norm_scalarHead_le_norm_image T δ hδ d N a))

end BP

theorem basisDecay_of_not_containsLinearCopy (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hno : ¬ ContainsLinearCopy ScalarC0 E) : BasisDecay E := by
  intro T
  by_contra hnot
  exact hno (BP.containsLinearCopy_of_not_tendsto_norm_image_scalarBasis T hnot)

end BanachGeometry
