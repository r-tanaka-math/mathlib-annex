import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.DyadicScalar
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.SignedEffectList

/-!
# Dyadic effects in the original C*-algebra

Everything is built by real continuous functional calculus in the given
algebra.  The base and tail effects, their order bounds, the real state
values and their square-root costs are explicit.  SOURCE_UNBUILT.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
open Finset
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear.Analytic

open MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]

def baseEffect (T : ℝ) (a : A) : A := cfc (baseSlice T) a

def tailEffect (L : ℝ) (a : A) : A := cfc (softSlice L) a

def fourthMoment (phi : A →L[ℂ] ℂ) (a : A) : ℝ := (phi (a ^ 4)).re

theorem baseEffect_nonneg {T : ℝ} (hT : 0 < T) (a : A) : 0 ≤ baseEffect T a :=
  cfc_nonneg (fun x _ ↦ baseSlice_nonneg hT x)

theorem baseEffect_le_one {T : ℝ} (hT : 0 < T) (a : A) : baseEffect T a ≤ 1 :=
  cfc_le_one _ _ (fun x _ ↦ baseSlice_le_one hT x)

theorem tailEffect_nonneg {L : ℝ} (hL : 0 < L) (a : A) : 0 ≤ tailEffect L a :=
  cfc_nonneg (fun x _ ↦ softSlice_nonneg hL x)

theorem tailEffect_le_one {L : ℝ} (hL : 0 < L) (a : A) : tailEffect L a ≤ 1 :=
  cfc_le_one _ _ (fun x _ ↦ softSlice_le_one hL x)

/-- The fourth-power majorant is an actual order inequality in `A`. -/
theorem tailEffect_le_fourth {L : ℝ} (hL : 0 < L) (a : A) (ha : IsSelfAdjoint a) :
    tailEffect L a ≤ (L ^ 4)⁻¹ • (a ^ 4) := by
  have hmono : cfc (softSlice L) a ≤ cfc (fun x : ℝ ↦ (L ^ 4)⁻¹ * x ^ 4) a := by
    apply cfc_mono
    · intro x _
      simpa [div_eq_mul_inv, mul_comm] using softSlice_le_fourth hL x
    · exact (continuous_softSlice L).continuousOn
    · exact (continuous_const.mul (continuous_id.pow 4)).continuousOn
  rw [cfc_const_mul (L ^ 4)⁻¹ (fun x : ℝ ↦ x ^ 4) a
    (continuous_id.pow 4).continuousOn,
    cfc_pow_id a 4 ha] at hmono
  exact hmono

/-- Positivity of the fourth power is not asserted for nonselfadjoint inputs. -/
theorem selfAdjoint_fourth_nonneg (a : A) (ha : IsSelfAdjoint a) : 0 ≤ a ^ 4 := by
  have hc : 0 ≤ cfc (fun x : ℝ ↦ x ^ 4) a := cfc_nonneg (by intros; positivity)
  rwa [cfc_pow_id a 4 ha] at hc

theorem fourthMoment_nonneg (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (a : A) (ha : IsSelfAdjoint a) : 0 ≤ fourthMoment phi a :=
  (RCLike.nonneg_iff.mp (hphi.1 _ (selfAdjoint_fourth_nonneg a ha))).1

@[simp] theorem fourthMoment_neg (phi : A →L[ℂ] ℂ) (a : A) :
    fourthMoment phi (-a) = fourthMoment phi a := by
  have hpow : (-a) ^ 4 = a ^ 4 := by noncomm_ring
  simp only [fourthMoment, hpow]

/-- The real coordinate of a positive functional is order preserving. -/
theorem state_re_mono (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {a b : A} (hab : a ≤ b) : (phi a).re ≤ (phi b).re := by
  have h := (RCLike.nonneg_iff.mp (hphi.1 (b - a) (sub_nonneg.mpr hab))).1
  rw [map_sub] at h
  change 0 ≤ (phi b).re - (phi a).re at h
  exact sub_nonneg.mp h

theorem state_re_real_smul (phi : A →L[ℂ] ℂ) (c : ℝ) (a : A) :
    (phi (c • a)).re = c * (phi a).re := by
  rw [ContinuousLinearMap.map_smul_of_tower,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp [smul_eq_mul, Complex.mul_re]

/-- One dyadic tail has the required state fourth-moment bound. -/
theorem tailEffect_state_re_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {L : ℝ} (hL : 0 < L) (a : A) (ha : IsSelfAdjoint a) :
    (phi (tailEffect L a)).re ≤ fourthMoment phi a / L ^ 4 := by
  have h := state_re_mono phi hphi (tailEffect_le_fourth hL a ha)
  rw [state_re_real_smul] at h
  simpa [fourthMoment, div_eq_mul_inv, mul_comm] using h

/-- No limiting argument is hidden in the cost of an individual tail. -/
theorem tailEffect_cost_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {L : ℝ} (hL : 0 < L) (a : A) (ha : IsSelfAdjoint a) :
    |L| * Real.sqrt (phi (tailEffect L a)).re ≤
      Real.sqrt (fourthMoment phi a) / L := by
  rw [abs_of_pos hL]
  apply weighted_sqrt_le_of_fourth_bound hL
  · exact (RCLike.nonneg_iff.mp (hphi.1 _ (tailEffect_nonneg hL a))).1
  · exact fourthMoment_nonneg phi hphi a ha
  · exact tailEffect_state_re_le phi hphi hL a ha

theorem baseEffect_cost_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {T : ℝ} (hT : 0 < T) (a : A) :
    |T| * Real.sqrt (phi (baseEffect T a)).re ≤ T := by
  obtain ⟨hs0, hs1, _⟩ := state_effect_coordinates phi hphi _
    (baseEffect_nonneg hT a) (baseEffect_le_one hT a)
  have hsqrt : Real.sqrt (phi (baseEffect T a)).re ≤ 1 := by
    nlinarith [Real.sq_sqrt hs0, Real.sqrt_nonneg (phi (baseEffect T a)).re]
  rw [abs_of_pos hT]
  nlinarith

/-- The finite list contains its actual base effect and actual dyadic tails. -/
def positiveSlices (T : ℝ) (a : A) : ℕ → List (ℝ × A)
  | 0 => [(T, baseEffect T a)]
  | N + 1 => (dyadicLevel T N, tailEffect (dyadicLevel T N) a) :: positiveSlices T a N

theorem hasEffects_positiveSlices {T : ℝ} (hT : 0 < T) (a : A) (N : ℕ) :
    HasEffects (positiveSlices T a N) := by
  induction N with
  | zero =>
      intro cp hcp
      simp only [positiveSlices, List.mem_singleton] at hcp
      subst cp
      exact ⟨baseEffect_nonneg hT a, baseEffect_le_one hT a⟩
  | succ N ih =>
      intro cp hcp
      rcases List.mem_cons.mp hcp with rfl | hcp
      · exact ⟨tailEffect_nonneg (dyadicLevel_pos hT N) a,
          tailEffect_le_one (dyadicLevel_pos hT N) a⟩
      · exact ih cp hcp

/-- Exact recovery of a truncated positive part. -/
theorem positiveSlices_value {T : ℝ} (hT : 0 < T) (a : A) (N : ℕ) :
    effectValue (positiveSlices T a N) = cfc (truncatePos (dyadicLevel T N)) a := by
  induction N with
  | zero =>
      simp only [positiveSlices, effectValue, add_zero, dyadicLevel_zero, baseEffect]
      rw [← cfc_const_mul T (baseSlice T) a (continuous_baseSlice T).continuousOn]
      apply cfc_congr
      intro x _
      unfold baseSlice
      field_simp [ne_of_gt hT]
  | succ N ih =>
      simp only [positiveSlices, effectValue, ih, tailEffect, dyadicLevel_succ]
      rw [← cfc_const_mul (dyadicLevel T N) (softSlice (dyadicLevel T N)) a
        (continuous_softSlice _).continuousOn]
      rw [← cfc_add a (fun x : ℝ ↦ dyadicLevel T N * softSlice (dyadicLevel T N) x)
        (truncatePos (dyadicLevel T N))
        ((continuous_const.mul (continuous_softSlice _)).continuousOn)
        (continuous_truncatePos _).continuousOn]
      apply cfc_congr
      intro x _
      dsimp only
      rw [level_mul_softSlice (dyadicLevel_pos hT N)]
      ring

/-- The cost before estimating its finite geometric sum. -/
theorem positiveSlices_cost_le_sum (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {T : ℝ} (hT : 0 < T) (a : A) (ha : IsSelfAdjoint a) (N : ℕ) :
    effectCost phi (positiveSlices T a N) ≤ T +
      ∑ k ∈ range N, Real.sqrt (fourthMoment phi a) / dyadicLevel T k := by
  induction N with
  | zero => simpa [positiveSlices, effectCost] using baseEffect_cost_le phi hphi hT a
  | succ N ih =>
      simp only [positiveSlices, effectCost, sum_range_succ]
      have ht := tailEffect_cost_le phi hphi (dyadicLevel_pos hT N) a ha
      linarith

/-- The finite dyadic sum is uniformly bounded, independent of `N`. -/
theorem reciprocal_level_sum_le {T m : ℝ} (hT : 0 < T) (N : ℕ) :
    ∑ k ∈ range N, Real.sqrt m / dyadicLevel T k ≤ 2 * Real.sqrt m / T := by
  have heq : (∑ k ∈ range N, Real.sqrt m / dyadicLevel T k) =
      (Real.sqrt m / T) * ∑ k ∈ range N, (1 : ℝ) / 2 ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold dyadicLevel
    field_simp [ne_of_gt hT] <;> ring
  rw [heq]
  have h : (Real.sqrt m / T) * ∑ k ∈ range N, (1 : ℝ) / 2 ^ k ≤
      (Real.sqrt m / T) * 2 :=
    mul_le_mul_of_nonneg_left (dyadic_reciprocal_sum_le N)
      (div_nonneg (Real.sqrt_nonneg m) hT.le)
  calc
    _ ≤ (Real.sqrt m / T) * 2 := h
    _ = 2 * Real.sqrt m / T := by ring

theorem positiveSlices_cost_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {T : ℝ} (hT : 0 < T) (a : A) (ha : IsSelfAdjoint a) (N : ℕ) :
    effectCost phi (positiveSlices T a N) ≤
      T + 2 * Real.sqrt (fourthMoment phi a) / T := by
  have h1 := positiveSlices_cost_le_sum phi hphi hT a ha N
  have h2 := reciprocal_level_sum_le (m := fourthMoment phi a) hT N
  linarith

end MathlibAnnex.CStarBilinear.Analytic
