/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Analysis.Normed.GeometricStructure.MaximalFace
public import MathlibAnnex.Analysis.Normed.GeometricStructure.ReflexiveSupport

/-!
# Smooth spaces and the original face-defined geometric structure space

Smoothness is used in its defining normed-space sense: the norming functionals
at each nonzero vector form a singleton. Nonemptiness is already supplied by
Hahn--Banach, so the explicit hypothesis below is precisely uniqueness.
It is not an assumption that the geometric structure family consists of kernels.

For a maximal face, select one of its unit vectors and apply this uniqueness to
all supporting functionals. Conversely a norm-attaining norm-one functional
exposes the maximal face through its attaining vector. Analytic reflexivity is
then used to obtain the family of all nonzero continuous-dual kernels.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (hsmooth : ∀ x : E, x ≠ 0 → (normingFunctionals 𝕜 x).Subsingleton)
include hsmooth

section Faces

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- In a smooth space the supporting functionals of any maximal face are unique. -/
theorem IsMaximalFace.subsingleton_supportFunctionals_of_smooth {M : Set E}
    (hM : IsMaximalFace M) : (supportFunctionals 𝕜 M).Subsingleton := by
  obtain ⟨x, hx⟩ := hM.nonempty
  have hxnorm : ‖x‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hM.subset_sphere hx
  have hxne : x ≠ 0 := by
    intro hxzero
    have : (0 : ℝ) = 1 := by simpa only [hxzero, norm_zero] using hxnorm
    exact zero_ne_one this
  intro f hf g hg
  apply hsmooth x hxne
  · exact ⟨hf.1, by simpa [hxnorm] using hf.2 x hx⟩
  · exact ⟨hg.1, by simpa [hxnorm] using hg.2 x hx⟩

/-- Smoothness turns the existing nonempty support family into an actual singleton. -/
theorem IsMaximalFace.supportFunctionals_eq_singleton_of_smooth {M : Set E}
    (hM : IsMaximalFace M) {f : StrongDual 𝕜 E} (hf : f ∈ supportFunctionals 𝕜 M) :
    supportFunctionals 𝕜 M = {f} := by
  apply Set.ext
  intro g
  constructor
  · intro hg
    exact Set.mem_singleton_iff.2
      (hM.subsingleton_supportFunctionals_of_smooth 𝕜 hsmooth hg hf)
  · intro hg
    rcases Set.mem_singleton_iff.1 hg with rfl
    exact hf

/-- In a smooth space a nonempty norm-one slice is a maximal face, with the
specified functional as its unique support. No replacement functional is used. -/
theorem isMaximalFace_unitBallSupportFace_of_smooth {f : StrongDual 𝕜 E}
    (hf : ‖f‖ = 1) (hne : (unitBallSupportFace 𝕜 f).Nonempty) :
    IsMaximalFace (unitBallSupportFace 𝕜 f) := by
  obtain ⟨x, hx⟩ := hne
  have hxsphere := unitBallSupportFace_subset_sphere 𝕜 hf.le hx
  have hxnorm : ‖x‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hxsphere
  have hxne : x ≠ 0 := by
    intro hxzero
    have : (0 : ℝ) = 1 := by simpa only [hxzero, norm_zero] using hxnorm
    exact zero_ne_one this
  obtain ⟨M, hxM, hM⟩ := exists_isMaximalFace_of_mem_sphere hxsphere
  obtain ⟨g, hg⟩ := hM.nonempty_supportFunctionals 𝕜
  have hgf : g = f := hsmooth x hxne
    ⟨hg.1, by simpa [hxnorm] using hg.2 x hxM⟩
    ⟨hf.le, by simpa [hxnorm] using hx.2⟩
  subst g
  exact (hM.eq_unitBallSupportFace 𝕜 hg) ▸ hM

/-- The unique support is exactly the initially specified norm-one functional. -/
theorem supportFunctionals_unitBallSupportFace_eq_singleton_of_smooth
    {f : StrongDual 𝕜 E} (hf : ‖f‖ = 1) (hne : (unitBallSupportFace 𝕜 f).Nonempty) :
    supportFunctionals 𝕜 (unitBallSupportFace 𝕜 f) = {f} := by
  have hmax := isMaximalFace_unitBallSupportFace_of_smooth 𝕜 hsmooth hf hne
  exact hmax.supportFunctionals_eq_singleton_of_smooth 𝕜 hsmooth
    ⟨hf.le, fun x hx => hx.2⟩

end Faces

/-- Smoothness alone makes every original geometric-structure point a norm-one kernel. -/
theorem exists_norm_eq_one_preimage_zero_eq_of_mem_geometricStructureFamily_of_smooth
    {I : Set E} (hI : I ∈ geometricStructureFamily 𝕜 E) :
    ∃ f : StrongDual 𝕜 E, ‖f‖ = 1 ∧ (f : E → 𝕜) ⁻¹' {0} = I := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨M, hM, hMI⟩ := hI
  obtain ⟨f, hf⟩ := hM.nonempty_supportFunctionals 𝕜
  have hfsingle := hM.supportFunctionals_eq_singleton_of_smooth 𝕜 hsmooth hf
  refine ⟨f, norm_eq_one_of_mem_supportFunctionals 𝕜 hM.nonempty
    (fun x hx => mem_closedBall_zero_iff.1 (hM.subset_closedBall hx)) hf, ?_⟩
  exact (supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton
    𝕜 M f hfsingle).symm.trans hMI

/-- A norm-attaining norm-one functional gives a point of the original face-defined family. -/
theorem preimage_zero_mem_geometricStructureFamily_of_smooth_of_nonempty_unitBallSupportFace
    {f : StrongDual 𝕜 E} (hf : ‖f‖ = 1) (hne : (unitBallSupportFace 𝕜 f).Nonempty) :
    (f : E → 𝕜) ⁻¹' {0} ∈ geometricStructureFamily 𝕜 E := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  refine ⟨unitBallSupportFace 𝕜 f,
    isMaximalFace_unitBallSupportFace_of_smooth 𝕜 hsmooth hf hne, ?_⟩
  exact supportKernelUnion_eq_preimage_zero_of_supportFunctionals_eq_singleton
    𝕜 _ f (supportFunctionals_unitBallSupportFace_eq_singleton_of_smooth 𝕜 hsmooth hf hne)

/-- Every nonzero continuous functional on a reflexive smooth space supplies an actual
geometric-structure point. The support witness comes from the double-dual API. -/
theorem preimage_zero_mem_geometricStructureFamily_of_smooth_of_surjective_inclusionInDoubleDual
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E))
    {f : StrongDual 𝕜 E} (hf : f ≠ 0) :
    (f : E → 𝕜) ⁻¹' {0} ∈ geometricStructureFamily 𝕜 E := by
  obtain ⟨g, hgnorm, hgker⟩ := exists_norm_eq_one_preimage_zero_eq_of_ne_zero 𝕜 hf
  rw [← hgker]
  exact preimage_zero_mem_geometricStructureFamily_of_smooth_of_nonempty_unitBallSupportFace
    𝕜 hsmooth hgnorm
      (nonempty_unitBallSupportFace_of_surjective_inclusionInDoubleDual 𝕜 hreflexive hgnorm)

/-- The full dual-kernel presentation in Example 4.10, proved from smoothness and
analytic reflexivity. This statement also handles the zero space: both sides are empty. -/
theorem mem_geometricStructureFamily_iff_exists_ne_zero_dual_of_smooth_of_reflexive
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E)) (I : Set E) :
    I ∈ geometricStructureFamily 𝕜 E ↔
      ∃ f : StrongDual 𝕜 E, f ≠ 0 ∧ (f : E → 𝕜) ⁻¹' {0} = I := by
  constructor
  · intro hI
    obtain ⟨f, hf, hker⟩ :=
      exists_norm_eq_one_preimage_zero_eq_of_mem_geometricStructureFamily_of_smooth 𝕜 hsmooth hI
    refine ⟨f, ?_, hker⟩
    intro hfzero
    have : (0 : ℝ) = 1 := by simpa only [hfzero, norm_zero] using hf
    exact zero_ne_one this
  · rintro ⟨f, hf, rfl⟩
    exact preimage_zero_mem_geometricStructureFamily_of_smooth_of_surjective_inclusionInDoubleDual
      𝕜 hsmooth hreflexive hf

/-- Set-family form of the reflexive smooth kernel presentation. -/
theorem geometricStructureFamily_eq_nonzero_dual_kernels_of_smooth_of_reflexive
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 E)) :
    geometricStructureFamily 𝕜 E =
      {I : Set E | ∃ f : StrongDual 𝕜 E, f ≠ 0 ∧ (f : E → 𝕜) ⁻¹' {0} = I} :=
  Set.ext (mem_geometricStructureFamily_iff_exists_ne_zero_dual_of_smooth_of_reflexive
    𝕜 hsmooth hreflexive)

end NormedSpace
