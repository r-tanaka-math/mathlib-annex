/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.L1SupportFace
public import MathlibAnnex.Analysis.Normed.Lp.L1DualExtreme
public import MathlibAnnex.Analysis.Normed.GeometricStructure.WeakStarMaximalFace

/-!
# The original ℓ¹ geometric structure family as unimodular kernels

The forward implication starts at an actual maximal face. Its extreme support
has unimodular coefficients by a proved coordinate perturbation argument, and
the previously proved singleton support family turns the union of supporting
kernels into its individual kernel. The reverse implication uses the proved
maximality of the unimodular support slice. No kernel-family representation is
an input hypothesis. The nonempty-index condition is essential: on an empty
index type the original GSS is empty, whereas the vacuous unimodularity condition
would select the zero functional.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set
open scoped lp ENNReal

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {ι : Type u} [DecidableEq ι]

section Faces

variable [Nonempty ι]
variable [NormedSpace ℝ ℓ¹(ι, 𝕜)] [IsScalarTower ℝ 𝕜 ℓ¹(ι, 𝕜)]

/-- The maximal-face characterization in REF42 Lemma 5.7. -/
theorem isMaximalFace_l1_iff (M : Set ℓ¹(ι, 𝕜)) :
    IsMaximalFace M ↔ ∃ u : ℓ^∞(ι, 𝕜), (∀ i, ‖u i‖ = 1) ∧
      M = unitBallSupportFace 𝕜 (lp.coefficientFunctional u) := by
  constructor
  · intro hM
    obtain ⟨f, hfnorm, hfext, hMF⟩ := hM.exists_extreme_eq_unitBallSupportFace 𝕜
    refine ⟨lp.dualCoefficients f,
      fun i => lp.norm_dualCoefficients_apply_eq_one_of_mem_extremePoints hfext i, ?_⟩
    exact hMF.trans (congrArg (unitBallSupportFace 𝕜)
      (lp.coefficientFunctional_dualCoefficients f).symm)
  · rintro ⟨u, hu, rfl⟩
    exact isMaximalFace_unitBallSupportFace_coefficientFunctional 𝕜 u hu

end Faces

/-- Every original ℓ¹ GSS point is a kernel of unimodular coefficients. -/
theorem exists_unimodular_preimage_zero_eq_of_mem_geometricStructureFamily_l1
    {I : Set ℓ¹(ι, 𝕜)} (hI : I ∈ geometricStructureFamily 𝕜 ℓ¹(ι, 𝕜)) :
    ∃ u : ℓ^∞(ι, 𝕜), (∀ i, ‖u i‖ = 1) ∧
      (lp.coefficientFunctional u : ℓ¹(ι, 𝕜) → 𝕜) ⁻¹' {0} = I := by
  letI : NormedSpace ℝ ℓ¹(ι, 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 ℓ¹(ι, 𝕜)
  letI : Module ℝ ℓ¹(ι, 𝕜) :=
    (NormedSpace.restrictScalars ℝ 𝕜 ℓ¹(ι, 𝕜)).toModule
  letI : IsScalarTower ℝ 𝕜 ℓ¹(ι, 𝕜) := IsScalarTower.restrictScalars ℝ 𝕜 ℓ¹(ι, 𝕜)
  obtain ⟨M, hM, hMI⟩ := hI
  obtain ⟨f, hfnorm, hfext, hMF⟩ := hM.exists_extreme_eq_unitBallSupportFace 𝕜
  let u := lp.dualCoefficients f
  have hu : ∀ i, ‖u i‖ = 1 :=
    fun i => lp.norm_dualCoefficients_apply_eq_one_of_mem_extremePoints hfext i
  have hfu : lp.coefficientFunctional u = f := lp.coefficientFunctional_dualCoefficients f
  have hs : supportFunctionals 𝕜 M = {lp.coefficientFunctional u} := by
    rw [hMF, ← hfu]
    exact supportFunctionals_unitBallSupportFace_coefficientFunctional_eq_singleton 𝕜 u hu
  refine ⟨u, hu, ?_⟩
  exact (supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton
    𝕜 M _ hs).symm.trans hMI

/-- The unimodular kernel presentation of ℓ¹, derived from the original face definition. -/
theorem mem_geometricStructureFamily_l1_iff [Nonempty ι] (I : Set ℓ¹(ι, 𝕜)) :
    I ∈ geometricStructureFamily 𝕜 ℓ¹(ι, 𝕜) ↔
      ∃ u : ℓ^∞(ι, 𝕜), (∀ i, ‖u i‖ = 1) ∧
        (lp.coefficientFunctional u : ℓ¹(ι, 𝕜) → 𝕜) ⁻¹' {0} = I := by
  constructor
  · exact exists_unimodular_preimage_zero_eq_of_mem_geometricStructureFamily_l1 𝕜
  · rintro ⟨u, hu, rfl⟩
    exact preimage_zero_coefficientFunctional_mem_geometricStructureFamily 𝕜 u hu

/-- The natural-number sequence formulation in Example 4.11 and REF42 Theorem 5.8. -/
theorem mem_geometricStructureFamily_l1_nat_iff (I : Set ℓ¹(ℕ, 𝕜)) :
    I ∈ geometricStructureFamily 𝕜 ℓ¹(ℕ, 𝕜) ↔
      ∃ (u : ℕ → 𝕜) (hu : ∀ n, ‖u n‖ = 1),
        (lp.coefficientFunctional (lp.inftyOfNormOne u hu) : ℓ¹(ℕ, 𝕜) → 𝕜) ⁻¹' {0} = I := by
  constructor
  · intro hI
    obtain ⟨u, hu, hker⟩ := (mem_geometricStructureFamily_l1_iff 𝕜 I).1 hI
    refine ⟨fun n => u n, hu, ?_⟩
    change (lp.coefficientFunctional u : ℓ¹(ℕ, 𝕜) → 𝕜) ⁻¹' {0} = I
    exact hker
  · rintro ⟨u, hu, rfl⟩
    exact preimage_zero_coefficientFunctional_mem_geometricStructureFamily 𝕜
      (lp.inftyOfNormOne u hu) hu

end NormedSpace
