/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.Lp.L1Dual
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFace

/-!
# Maximal faces exposed by unimodular ℓ¹ coefficients

Every coordinate supplies a vector in the value-one slice. Consequently every
supporting functional of that slice has the specified coefficients. This proves
uniqueness rather than assuming it, and maximal-face extension then proves that
the slice itself is maximal. In the empty-index case there is no maximal face;
only maximality and the resulting GSS membership require a nonempty index type.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped lp ENNReal

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {ι : Type u} [DecidableEq ι]

/-- The inverse-coefficient coordinate vector lies in the specified support slice. -/
theorem single_inv_mem_unitBallSupportFace_coefficientFunctional
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1) (i : ι) :
    lp.single 1 i (u i)⁻¹ ∈ unitBallSupportFace 𝕜 (lp.coefficientFunctional u) := by
  have hui : u i ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  constructor
  · simpa only [mem_closedBall_zero_iff,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_inv, hu, inv_one]
      using (show (1 : ℝ) ≤ 1 from le_rfl)
  · change lp.coefficientFunctional u
      (lp.single (E := fun _ : ι => 𝕜) 1 i (u i)⁻¹) = 1
    rw [lp.coefficientFunctional_single, inv_mul_cancel₀ hui]

/-- A functional supporting the whole unimodular slice is the specified one. -/
theorem eq_coefficientFunctional_of_mem_supportFunctionals_unitBallSupportFace
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1)
    {g : StrongDual 𝕜 ℓ¹(ι, 𝕜)}
    (hg : g ∈ supportFunctionals 𝕜 (unitBallSupportFace 𝕜 (lp.coefficientFunctional u))) :
    g = lp.coefficientFunctional u := by
  have hcoeff : lp.dualCoefficients g = u := by
    apply Subtype.ext
    funext i
    change g (lp.single 1 i (1 : 𝕜)) = u i
    have hui : u i ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
    have hs : lp.single (E := fun _ : ι => 𝕜) 1 i (u i)⁻¹ =
        (u i)⁻¹ • lp.single 1 i (1 : 𝕜) := by
      simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ι => 𝕜) 1 i (u i)⁻¹ (1 : 𝕜)
    have hgi : (u i)⁻¹ * g (lp.single 1 i (1 : 𝕜)) = 1 := by
      simpa only [hs, map_smul, smul_eq_mul] using
        hg.2 _ (single_inv_mem_unitBallSupportFace_coefficientFunctional 𝕜 u hu i)
    calc
      g (lp.single 1 i 1) = u i * ((u i)⁻¹ * g (lp.single 1 i 1)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hui, one_mul]
      _ = u i := by rw [hgi, mul_one]
  rw [← lp.coefficientFunctional_dualCoefficients g, hcoeff]

/-- The entire supporting family, not merely its extreme points, is a singleton. -/
theorem supportFunctionals_unitBallSupportFace_coefficientFunctional_eq_singleton
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1) :
    supportFunctionals 𝕜 (unitBallSupportFace 𝕜 (lp.coefficientFunctional u)) =
      {lp.coefficientFunctional u} := by
  have hnorm : ‖lp.coefficientFunctional u‖ ≤ 1 := by
    rw [lp.norm_coefficientFunctional]
    exact lp.norm_le_of_forall_le zero_le_one (fun i => (hu i).le)
  ext g
  constructor
  · intro hg
    exact Set.mem_singleton_iff.2
      (eq_coefficientFunctional_of_mem_supportFunctionals_unitBallSupportFace 𝕜 u hu hg)
  · rintro rfl
    exact ⟨hnorm, fun x hx => hx.2⟩

section Maximality

variable [Nonempty ι]
variable [NormedSpace ℝ ℓ¹(ι, 𝕜)] [IsScalarTower ℝ 𝕜 ℓ¹(ι, 𝕜)]

/-- The unimodular value-one slice is a maximal proper real convex face. -/
theorem isMaximalFace_unitBallSupportFace_coefficientFunctional
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1) :
    IsMaximalFace (unitBallSupportFace 𝕜 (lp.coefficientFunctional u)) := by
  classical
  have hnorm := lp.norm_coefficientFunctional_eq_one_of_forall_norm_eq_one u hu
  have hne : (unitBallSupportFace 𝕜 (lp.coefficientFunctional u)).Nonempty :=
    ⟨lp.single 1 (Classical.arbitrary ι) (u (Classical.arbitrary ι))⁻¹,
      single_inv_mem_unitBallSupportFace_coefficientFunctional 𝕜 u hu _⟩
  obtain ⟨M, hFM, hM⟩ := exists_isMaximalFace_of_convex_subset_sphere hne
    (convex_unitBallSupportFace 𝕜 _) (unitBallSupportFace_subset_sphere 𝕜 hnorm.le)
  obtain ⟨g, hg⟩ := hM.nonempty_supportFunctionals 𝕜
  have hgf : g = lp.coefficientFunctional u :=
    eq_coefficientFunctional_of_mem_supportFunctionals_unitBallSupportFace 𝕜 u hu
      ⟨hg.1, fun a ha => hg.2 a (hFM ha)⟩
  have hMF := hM.eq_unitBallSupportFace 𝕜 hg
  rw [hgf] at hMF
  exact hMF ▸ hM

end Maximality

/-- A unimodular coefficient kernel belongs to the original face-defined GSS. -/
theorem preimage_zero_coefficientFunctional_mem_geometricStructureFamily [Nonempty ι]
    (u : ℓ^∞(ι, 𝕜)) (hu : ∀ i, ‖u i‖ = 1) :
    (lp.coefficientFunctional u : ℓ¹(ι, 𝕜) → 𝕜) ⁻¹' {0} ∈
      geometricStructureFamily 𝕜 ℓ¹(ι, 𝕜) := by
  letI : NormedSpace ℝ ℓ¹(ι, 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 ℓ¹(ι, 𝕜)
  refine ⟨unitBallSupportFace 𝕜 (lp.coefficientFunctional u),
    isMaximalFace_unitBallSupportFace_coefficientFunctional 𝕜 u hu, ?_⟩
  exact supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton 𝕜 _ _
    (supportFunctionals_unitBallSupportFace_coefficientFunctional_eq_singleton 𝕜 u hu)

end NormedSpace
