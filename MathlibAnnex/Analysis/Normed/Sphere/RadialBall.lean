import MathlibAnnex.Analysis.Normed.Sphere.RadialExtension
import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Transport

/-! # Radial image of equivalent seminorm unit balls
The model norm lives on `Space M`; the underlying finite Pi carrier retains its
reference norm. All radial maps below use the accepted radialExtension exactly.
No positive-dimension hypothesis is needed for the ball image or distance bounds.
-/

noncomputable section
open Set Metric Function
open scoped NNReal ENNReal
namespace MathlibAnnex.Sphere
open EquivalentSeminorm

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
  have h := (lipschitzWith_radialExtension Δ).dist_le_mul
    (show Space MX from x) (show Space MX from y)
  simpa only [dist_space_eq, NNReal.coe_ofNat] using h

private theorem lipschitzWith_radialMap {n : ℕ}
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

namespace Internal
private def modelRadialAntiConstant {n : ℕ} (MX MY : EquivalentSeminorm (Fin n → ℝ)) : ℝ :=
  MX.lower / (3 * MY.upper)

private theorem modelRadialAntiConstant_pos {n : ℕ} (MX MY : EquivalentSeminorm (Fin n → ℝ)) :
    0 < modelRadialAntiConstant MX MY :=
  div_pos MX.lower_pos (mul_pos (by norm_num) MY.upper_pos)
end Internal
open Internal

private theorem radialMap_lower {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) (x y : Fin n → ℝ) :
    modelRadialAntiConstant MX MY * ‖x - y‖ ≤ ‖radialMap Δ x - radialMap Δ y‖ := by
  have hinv := radialMap_model_dist Δ.symm (radialMap Δ x) (radialMap Δ y)
  rw [radialMap_leftInverse Δ x, radialMap_leftInverse Δ y] at hinv
  have hlow := MX.lower_le (x - y)
  have hup := MY.le_upper (radialMap Δ x - radialMap Δ y)
  have hden : 0 < 3 * MY.upper := mul_pos (by norm_num) MY.upper_pos
  have hprod : MX.lower * ‖x - y‖ ≤ (3 * MY.upper) *
      ‖radialMap Δ x - radialMap Δ y‖ := by nlinarith
  dsimp [modelRadialAntiConstant]
  calc
    MX.lower / (3 * MY.upper) * ‖x - y‖ =
      (MX.lower * ‖x - y‖) / (3 * MY.upper) := by ring
    _ ≤ ‖radialMap Δ x - radialMap Δ y‖ :=
      (div_le_iff₀ hden).2 (by simpa only [mul_comm] using hprod)

private theorem isOpen_seminorm_ball {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    IsOpen (M.p.ball 0 1) := by
  rw [Seminorm.ball_zero_eq]
  exact isOpen_lt M.continuous_p continuous_const

private theorem convex_seminorm_ball {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    Convex ℝ (M.p.ball 0 1) := M.p.convex_ball 0 1

private theorem isConnected_seminorm_ball {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    IsConnected (M.p.ball 0 1) := by
  refine (convex_seminorm_ball M).isConnected ?_
  exact ⟨0, by simp⟩

namespace Internal

/-- Identity equivalence between the metric sphere of the model copy and its
seminorm level set on reference coordinates. -/
private def modelSphereCopyEquiv {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    sphere (0 : Space M) 1 ≃ M.unitSphere where
  toFun u := ⟨(show Fin n → ℝ from u.val), sphere_apply M u⟩
  invFun u := ⟨(show Space M from u.val), mem_sphere_zero_iff_norm.mpr u.property⟩
  left_inv u := by cases u; rfl
  right_inv u := by cases u; rfl

/-- Under the frozen ModelSphereIso substitution the ordinary sphere isometry
is already the input; transport is the identity. -/
private def modelSphereIsoToSphereIso {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1 := Δ

@[simp] private theorem modelSphereIsoToSphereIso_symm {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    modelSphereIsoToSphereIso Δ.symm = (modelSphereIsoToSphereIso Δ).symm := rfl

private theorem antilipschitzWith_radialMap {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    AntilipschitzWith (modelRadialAntiConstant MX MY).toNNReal⁻¹ (radialMap Δ) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro x y
  have h := radialMap_lower Δ x y
  have hc := modelRadialAntiConstant_pos MX MY
  have h' : ‖x - y‖ ≤ (modelRadialAntiConstant MX MY)⁻¹ *
      ‖radialMap Δ x - radialMap Δ y‖ := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).2 (by simpa only [mul_comm] using h)
  simpa only [dist_eq_norm, NNReal.coe_inv,
    Real.coe_toNNReal (modelRadialAntiConstant MX MY) hc.le] using h'
end Internal

/-- The accepted radial extension in reference coordinates maps the source open
unit seminorm ball exactly onto the target open unit seminorm ball. -/
theorem radialExtension_image_ball {n : ℕ}
    {MX MY : EquivalentSeminorm (Fin n → ℝ)}
    (Δ : sphere (0 : Space MX) 1 ≃ᵢ sphere (0 : Space MY) 1) :
    (fun x : Fin n → ℝ => (show Fin n → ℝ from
      radialExtension (X := Space MX) (Y := Space MY) Δ (show Space MX from x))) '' MX.p.ball 0 1 = MY.p.ball 0 1 := by
  change radialMap Δ '' MX.p.ball 0 1 = MY.p.ball 0 1
  simp only [Seminorm.ball_zero_eq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_setOf_eq, radialMap_p] using hx
  · intro hy
    refine ⟨radialMap Δ.symm y, ?_, ?_⟩
    · simpa only [mem_setOf_eq, radialMap_p] using hy
    · exact radialMap_leftInverse Δ.symm y

private theorem setOf_seminorm_lt_one_eq_ball {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    {x | M.p x < 1} = M.p.ball 0 1 := (Seminorm.ball_zero_eq M.p).symm

end MathlibAnnex.Sphere
