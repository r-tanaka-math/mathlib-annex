import MathlibAnnex.Analysis.LocallyConvex.FiniteApproximation
import MathlibAnnex.Analysis.Normed.Module.Goldstine

/-!
# Simultaneous real-linear finite approximation with an exact norm budget

Goldstine plus real convexity approximates every representable finite image
of a bidual point in norm.  The same source point meets all coordinates,
including heterogeneous target spaces.  Radius zero and empty finite test
families are included; no separability or sequence selection is used.

C02 controller-authored proof source; unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Topology

namespace MathlibAnnex.FiniteApproximation

universe u v w
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- One real-linear finite image, with the original bidual norm as radius. -/
theorem exists_ball_image_lt (F : StrongDual ℝ (StrongDual ℝ X))
    (T : X →L[ℝ] Z) (z : Z)
    (hz : ∀ g : StrongDual ℝ Z, F (g.comp T) = g z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : X, ‖a‖ ≤ ‖F‖ ∧ ‖T a - z‖ < ε := by
  by_cases hF : F = 0
  · have hz0 : z = 0 := by
      apply (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := Z)).injective
      ext g
      change g z = g (0 : Z)
      simpa [hF] using (hz g).symm
    exact ⟨0, by simpa only [norm_zero] using (norm_nonneg F),
      by simpa [hz0] using hε⟩
  · have hr : 0 < ‖F‖ := (norm_pos_iff (a := F)).2 hF
    let F₁ : StrongDual ℝ (StrongDual ℝ X) := ‖F‖⁻¹ • F
    let z₁ : Z := ‖F‖⁻¹ • z
    have hF₁ : ‖F₁‖ ≤ 1 := by
      calc
        ‖F₁‖ = ‖‖F‖⁻¹ • F‖ := rfl
        _ ≤ ‖(‖F‖⁻¹ : ℝ)‖ * ‖F‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
        _ = 1 := by
          rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg F)]
          exact inv_mul_cancel₀ hr.ne'
    have hclosure : InWeakStarClosure F₁ (Metric.closedBall 0 (1 : ℝ)) := by
      apply NormedSpace.closedBall_subset_closure_weakStarCanonicalImage
        (𝕜 := ℝ) (X := X)
      change dist F₁ 0 ≤ (1 : ℝ)
      exact (dist_zero_right F₁).symm ▸ hF₁
    have hz₁ : ∀ g : StrongDual ℝ Z, F₁ (g.comp T) = g z₁ := by
      intro g
      simp only [F₁, z₁, ContinuousLinearMap.smul_apply, map_smul, hz]
    obtain ⟨a, ha, he⟩ := exists_norm_sub_lt
      (convex_closedBall (0 : X) (1 : ℝ)) hclosure T z₁ hz₁ (div_pos hε hr)
    refine ⟨‖F‖ • a, ?_, ?_⟩
    · have ha' : ‖a‖ ≤ 1 := by simpa using ha
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simpa using mul_le_mul_of_nonneg_left ha' hr.le
    · have heq : T (‖F‖ • a) - z = ‖F‖ • (T a - z₁) := by
        simp [z₁, smul_sub, smul_smul, hr.ne']
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc
        ‖F‖ * ‖T a - z₁‖ < ‖F‖ * (ε / ‖F‖) := mul_lt_mul_of_pos_left he hr
        _ = ε := by field_simp

/-- The finite product coefficient identity, for genuinely heterogeneous
normed targets. This is proved by the actual coordinate injections. -/
theorem finite_pi_biddual_identity
    {ι : Type w} [Fintype ι] (Z : ι → Type v)
    [∀ i, NormedAddCommGroup (Z i)] [∀ i, NormedSpace ℝ (Z i)]
    (F : StrongDual ℝ (StrongDual ℝ X)) (T : ∀ i, X →L[ℝ] Z i)
    (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    (g : StrongDual ℝ (∀ i, Z i)) :
    F (g.comp (ContinuousLinearMap.pi T)) = g z := by
  classical
  have hsplit : g.comp (ContinuousLinearMap.pi T) =
      ∑ i, (g.comp (ContinuousLinearMap.single ℝ Z i)).comp (T i) := by
    ext a
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.pi_apply]
    exact (ContinuousLinearMap.sum_comp_single ℝ Z g (fun i => T i a)).symm
  rw [hsplit, map_sum]
  simp_rw [hz]
  exact ContinuousLinearMap.sum_comp_single ℝ Z g z

/-- A single point in the norm ball meets a finite heterogeneous family.
The norm bound does not grow with the size of the family. -/
theorem exists_ball_finite_image_lt
    {ι : Type w} [Fintype ι] (Z : ι → Type v)
    [∀ i, NormedAddCommGroup (Z i)] [∀ i, NormedSpace ℝ (Z i)]
    (F : StrongDual ℝ (StrongDual ℝ X)) (T : ∀ i, X →L[ℝ] Z i)
    (z : ∀ i, Z i)
    (hz : ∀ i (g : StrongDual ℝ (Z i)), F (g.comp (T i)) = g (z i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : X, ‖a‖ ≤ ‖F‖ ∧ ∀ i, ‖T i a - z i‖ < ε := by
  obtain ⟨a, ha, he⟩ := exists_ball_image_lt F (ContinuousLinearMap.pi T) z
    (finite_pi_biddual_identity Z F T z hz) hε
  refine ⟨a, ha, fun i => ?_⟩
  exact (norm_le_pi_norm ((ContinuousLinearMap.pi T) a - z) i).trans_lt he

/-- Component identities for a binary real product, without a choice of two
unrelated approximants. -/
theorem prod_biddual_identity
    {W : Type w} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : StrongDual ℝ (StrongDual ℝ X))
    (T : X →L[ℝ] Z) (S : X →L[ℝ] W) (z : Z) (w : W)
    (hz : ∀ g : StrongDual ℝ Z, F (g.comp T) = g z)
    (hw : ∀ g : StrongDual ℝ W, F (g.comp S) = g w)
    (g : StrongDual ℝ (Z × W)) : F (g.comp (T.prod S)) = g (z, w) := by
  let g₁ := g.comp (ContinuousLinearMap.inl ℝ Z W)
  let g₂ := g.comp (ContinuousLinearMap.inr ℝ Z W)
  have he : g.comp (T.prod S) = g₁.comp T + g₂.comp S := by
    ext a
    simpa [g₁, g₂] using map_add g (T a, 0) (0, S a)
  rw [he, map_add, hz, hw]
  simpa [g₁, g₂] using (map_add g (z, 0) (0, w)).symm

end MathlibAnnex.FiniteApproximation
