import MathlibAnnex.Analysis.Normed.Plucker.BoundaryExtension
import MathlibAnnex.Analysis.Normed.Plucker.RadialAverage
import MathlibAnnex.MeasureTheory.Integral.MaximalMinorBoundary
import MathlibAnnex.Analysis.Convex.PluckerBody

/-! # Plücker bodies are invariant under sphere isometries

The boundary extension supplies source-body membership. The accepted boundary
null-Lagrangian theorem transfers its derivative average to the radial map.
The radial average gives an explicit scalar sign, removed using generator sign
symmetry. Equality uses both inclusions, the first from the inverse isometry.
The source positive-dimension boundary `m + 1` is retained throughout.
-/

noncomputable section
open Set Metric Function MeasureTheory
open scoped NNReal ENNReal BigOperators
namespace MathlibAnnex.PluckerBody
open EquivalentSeminorm Sphere Plucker

-- Exact private coordinate adapters from the accepted B1/B2 sources.
private abbrev radialMap {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  show Fin n → ℝ from radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x)

@[simp] private theorem radialMap_p {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x : Fin n → ℝ) :
    MY.p (radialMap Δ x) = MX.p x := radialExtension_norm Δ (show Space MX from x)

private theorem radialMap_leftInverse {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    LeftInverse (radialMap Δ.symm) (radialMap Δ) :=
  fun x => radialExtension_leftInverse Δ (show Space MX from x)

private theorem radialMap_model_dist {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x y : Fin n → ℝ) :
    MY.p (radialMap Δ x - radialMap Δ y) ≤ 3 * MX.p (x - y) := by
  have h := (radialExtension_lipschitz Δ).dist_le_mul
    (show Space MX from x) (show Space MX from y)
  simpa only [dist_space_eq, NNReal.coe_ofNat] using h

private theorem radialMap_lipschitz {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    LipschitzWith (3 * MX.upper / MY.lower).toNNReal (radialMap Δ) := by
  have hC : 0 ≤ 3 * MX.upper / MY.lower := div_nonneg (mul_nonneg (by norm_num) MX.upper_pos.le) MY.lower_pos.le
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hlower := MY.lower_le (radialMap Δ x - radialMap Δ y)
  have hmodel := radialMap_model_dist Δ x y
  have hupper := MX.le_upper (x - y)
  rw [Real.coe_toNNReal _ hC, dist_eq_norm, dist_eq_norm]
  calc
    ‖radialMap Δ x - radialMap Δ y‖ ≤ (3 * MX.upper * ‖x - y‖) / MY.lower :=
      (le_div_iff₀ MY.lower_pos).2 (by nlinarith)
    _ = (3 * MX.upper / MY.lower) * ‖x - y‖ := by ring

private def coordinateBoundaryData {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) : MX.unitSphere → (Fin N → ℝ) :=
  fun u => A (show Fin (m + 1) → ℝ from
    (Δ ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩).val)

private theorem coordinateBoundaryData_modelLipschitz {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : Metric.sphere (0 : Space MX) 1 ≃ᵢ Metric.sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) (hA : MY.IsContraction A) :
    ∀ u v, ‖coordinateBoundaryData Δ A u - coordinateBoundaryData Δ A v‖ ≤
      MX.p ((u : Fin (m + 1) → ℝ) - (v : Fin (m + 1) → ℝ)) := by
  intro u v
  let u' : Metric.sphere (0 : Space MX) 1 :=
    ⟨(show Space MX from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩
  let v' : Metric.sphere (0 : Space MX) 1 :=
    ⟨(show Space MX from v.val), mem_sphere_zero_iff_norm.mpr v.property⟩
  have chord : MY.p ((show Fin (m + 1) → ℝ from (Δ u').val) -
      (show Fin (m + 1) → ℝ from (Δ v').val)) = MX.p (u.val - v.val) := by
    simpa only [Subtype.dist_eq, dist_space_eq] using Δ.isometry.dist_eq u' v'
  calc
    ‖coordinateBoundaryData Δ A u - coordinateBoundaryData Δ A v‖ =
        ‖A ((show Fin (m + 1) → ℝ from (Δ u').val) -
          (show Fin (m + 1) → ℝ from (Δ v').val))‖ := by
      simp [coordinateBoundaryData, u', v', map_sub]
    _ ≤ MY.p ((show Fin (m + 1) → ℝ from (Δ u').val) -
        (show Fin (m + 1) → ℝ from (Δ v').val)) := hA _
    _ = MX.p (u.val - v.val) := chord


private theorem derivativeGenerator_apply_eq {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ))
    (s : Matrix.MaximalMinorIndex n (Fin N))
    (f : (Fin n → ℝ) → (Fin N → ℝ)) (x : Fin n → ℝ) :
    derivativeGenerator M f x s =
      M.closedUnitBallVolume * NullLagrangian.maximalMinorIntegrand s f x := by
  simp only [derivativeGenerator, Matrix.ballVolumeScaledMaximalMinors,
    Pi.smul_apply, Matrix.maximalMinors, smul_eq_mul,
    NullLagrangian.maximalMinorIntegrand, ContinuousLinearMap.det_selectedSquare]

private theorem average_apply_eq_integral {n N : ℕ}
    (M : EquivalentSeminorm (Fin n → ℝ))
    (s : Matrix.MaximalMinorIndex n (Fin N)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (hint : IntegrableOn (derivativeGenerator M f) M.closedUnitBall volume) :
    derivativeAverage M f s =
      ∫ x in M.closedUnitBall, NullLagrangian.maximalMinorIntegrand s f x := by
  have hcoord : ∀ t : Matrix.MaximalMinorIndex n (Fin N),
      Integrable (fun x => derivativeGenerator M f x t)
        (volume.restrict M.closedUnitBall) := fun t => hint.eval t
  rw [derivativeAverage, setAverage_eq, Pi.smul_apply, MeasureTheory.eval_integral hcoord s]
  simp_rw [derivativeGenerator_apply_eq M s f]
  rw [integral_const_mul]
  change M.closedUnitBallVolume⁻¹ * (M.closedUnitBallVolume *
    (∫ x in M.closedUnitBall, NullLagrangian.maximalMinorIntegrand s f x)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt M.closedUnitBallVolume_pos), one_mul]

private theorem average_eq_of_trace {m N : ℕ}
    (M : EquivalentSeminorm (Fin (m + 1) → ℝ))
    {F G : (Fin (m + 1) → ℝ) → (Fin N → ℝ)} {CF CG : ℝ≥0}
    (hF : LipschitzWith CF F) (hG : LipschitzWith CG G)
    (htrace : ∀ x, M.p x = 1 → F x = G x) :
    derivativeAverage M F = derivativeAverage M G := by
  ext s
  rw [average_apply_eq_integral M s F
      (derivativeGenerator_integrableOn_compact M ⟨CF, hF⟩ M.closedUnitBall_isCompact),
    average_apply_eq_integral M s G
      (derivativeGenerator_integrableOn_compact M ⟨CG, hG⟩ M.closedUnitBall_isCompact)]
  exact NullLagrangian.integral_maximalMinor_eq_of_pointwise_boundary_eq
    M.p M.continuous_p M.closedUnitBall_isCompact s hF hG htrace

/-- A normalized target generator belongs to the source body under a unit-sphere isometry. -/
theorem normalizedGenerator_mem_of_sphereIsometry {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1)
    (A : (Fin (m + 1) → ℝ) →L[ℝ] (Fin N → ℝ)) (hA : MY.IsContraction A) :
    Matrix.ballVolumeScaledMaximalMinors MY A ∈ body MX N := by
  let g := coordinateBoundaryData Δ A
  -- SR-SOURCE-B72: obtain exactly the public existential's average-membership field.
  obtain ⟨f, hf, htrace, _hderiv, _hint, hmem⟩ :=
    exists_extension_with_derivativeAverage_mem MX g
      (coordinateBoundaryData_modelLipschitz Δ A hA)
  have hfl : LipschitzWith ⟨MX.upper, MX.upper_pos.le⟩ f := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change ‖f x - f y‖ ≤ MX.upper * ‖x - y‖
    exact (hf x y).trans (MX.le_upper (x - y))
  have hgl := A.lipschitz.comp (radialMap_lipschitz Δ)
  have hboundary : ∀ x, MX.p x = 1 → f x = A (radialMap Δ x) := by
    intro x hx
    rw [htrace ⟨x, hx⟩]
    dsimp [g, coordinateBoundaryData]
    congr 1
    exact (radialExtension_on_sphere Δ
      ⟨(show Space MX from x), mem_sphere_zero_iff_norm.mpr hx⟩).symm
  have havg := average_eq_of_trace MX hfl hgl hboundary
  obtain ⟨ε, hε, hs⟩ := derivativeAverage_comp_linear_radial Δ A
  have hs' : derivativeAverage MX (fun x => A (radialMap Δ x)) =
      ε • Matrix.ballVolumeScaledMaximalMinors MY A := hs
  have hsigned : ε • Matrix.ballVolumeScaledMaximalMinors MY A ∈ body MX N := by
    exact (havg.trans hs') ▸ hmem
  rcases hε with rfl | rfl
  · simpa only [one_smul] using hsigned
  · have hn : -Matrix.ballVolumeScaledMaximalMinors MY A ∈ body MX N := by
      simpa only [neg_one_smul] using hsigned
    simpa only [neg_neg] using body_neg MX hn

/-- Both signs of every raw target generator belong to the source body. -/
theorem rawGenerators_subset_of_sphereIsometry {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    generators MY N ⊆ body MX N := by
  rintro z ⟨A, hA, rfl | rfl⟩
  · exact normalizedGenerator_mem_of_sphereIsometry Δ A hA
  · exact body_neg MX (normalizedGenerator_mem_of_sphereIsometry Δ A hA)

/-- The target body is contained in the source body. -/
theorem subset_of_sphereIsometry {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    body MY N ⊆ body MX N := by
  exact convexHull_min (rawGenerators_subset_of_sphereIsometry Δ)
    (convex_convexHull ℝ (generators MX N))

/-- Equality follows from the two inclusions furnished by the isometry and its inverse. -/
theorem eq_of_sphereIsometry {m N : ℕ}
    {MX MY : EquivalentSeminorm (Fin (m + 1) → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    body MX N = body MY N := by
  apply Set.Subset.antisymm
  · exact subset_of_sphereIsometry Δ.symm
  · exact subset_of_sphereIsometry Δ

end MathlibAnnex.PluckerBody
