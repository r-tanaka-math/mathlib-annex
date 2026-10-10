/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.AffineSliceFace

/-!
# Specified supporting functionals and maximal orthogonality filters

A maximal face contained in a maximal filter has all its common supports in
that filter's absolute support family. In particular the specified functional,
not just a newly selected support, belongs to the family. The full phase
comparison of two common supports is proved separately.

No completeness is required. The phase comparison also treats the zero space;
there all value-one faces are empty. No new geometric-structure point is added.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Metric

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- Every common support of a maximal face is an absolute support on any
maximal orthogonality filter containing that face. -/
theorem IsMaximalFace.mem_absoluteNormingFunctionals_of_subset_maximal_filter
    {F U : Set E} (hF : IsMaximalFace F) (hU : IsMaximalBirkhoffJamesFilter 𝕜 U)
    (hFU : F ⊆ U) {f : StrongDual 𝕜 E} (hf : f ∈ supportFunctionals 𝕜 F) :
    ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x := by
  obtain ⟨g, hg⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
  obtain ⟨a, ha, hag⟩ := exists_norm_eq_one_smul_mem_supportFunctionals 𝕜
    hF.nonempty hF.convex hF.subset_sphere (fun x hx => hg x (hFU hx))
  let g₀ : StrongDual 𝕜 E := a • g
  have hg₀ : ∀ x ∈ U, g₀ ∈ absoluteNormingFunctionals 𝕜 x :=
    fun x hx => smul_mem_absoluteNormingFunctionals 𝕜 ha (hg x hx)
  have hface : F = unitBallSupportFace 𝕜 g₀ := hF.eq_unitBallSupportFace 𝕜 hag
  intro x hx
  refine ⟨hf.1, ?_⟩
  by_cases hx₀ : x = 0
  · simp only [hx₀, map_zero, norm_zero]
  have hgx : g₀ x ≠ 0 :=
    norm_ne_zero_iff.mp ((hg₀ x hx).2.trans_ne (norm_ne_zero_iff.mpr hx₀))
  have hnormalized : (g₀ x)⁻¹ • x ∈ F := by
    rw [hface]
    exact inv_apply_smul_mem_unitBallSupportFace 𝕜 (hg₀ x hx) hx₀
  have hvalue : (g₀ x)⁻¹ * f x = 1 := by
    simpa only [map_smul, smul_eq_mul] using hf.2 _ hnormalized
  have heq : f x = g₀ x := by
    calc
      f x = g₀ x * ((g₀ x)⁻¹ * f x) := by
        rw [← mul_assoc, mul_inv_cancel₀ hgx, one_mul]
      _ = g₀ x := by rw [hvalue, mul_one]
  rw [heq, (hg₀ x hx).2]

/-- A specified contractive functional whose value-one face is maximal
belongs to the common absolute support family of an actual maximal filter.
The norm-one case in Lemma 4.13 is a specialization of this statement. -/
theorem exists_isMaximalBirkhoffJamesFilter_forall_mem_absoluteNormingFunctionals
    {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) (hF : IsMaximalFace (unitBallSupportFace 𝕜 f)) :
    ∃ U : Set E, IsMaximalBirkhoffJamesFilter 𝕜 U ∧
      ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x := by
  obtain ⟨U, hFU, hU⟩ := exists_isMaximalBirkhoffJamesFilter_of_directed 𝕜 hF.nonempty
    (directed_birkhoffJamesOrthogonalSet_of_convex_subset_sphere 𝕜 hF.convex hF.subset_sphere)
  exact ⟨U, hU, hF.mem_absoluteNormingFunctionals_of_subset_maximal_filter 𝕜
    hU hFU ⟨hf, fun x hx => hx.2⟩⟩

/-- The maximal filter in the specified-support theorem can be taken to be
exactly the absolute norm-attainment set of that same functional. -/
theorem isMaximalBirkhoffJamesFilter_absoluteNormAttainmentSet_of_isMaximalFace
    {f : StrongDual 𝕜 E} (hf : ‖f‖ ≤ 1) (hF : IsMaximalFace (unitBallSupportFace 𝕜 f)) :
    IsMaximalBirkhoffJamesFilter 𝕜 (absoluteNormAttainmentSet 𝕜 f) := by
  obtain ⟨U, hU, hfU⟩ :=
    exists_isMaximalBirkhoffJamesFilter_forall_mem_absoluteNormingFunctionals 𝕜 hf hF
  rw [← hU.eq_absoluteNormAttainmentSet 𝕜 hfU]
  exact hU

/-- Full phase comparison: the first support is left unchanged, and the
second is multiplied by one scalar of norm one. This is not equality of
supporting functionals. -/
theorem IsMaximalBirkhoffJamesFilter.exists_unitBallSupportFace_eq_smul
    {U : Set E} (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f g : StrongDual 𝕜 E}
    (hf : ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x)
    (hg : ∀ x ∈ U, g ∈ absoluteNormingFunctionals 𝕜 x) :
    ∃ a : 𝕜, ‖a‖ = 1 ∧ unitBallSupportFace 𝕜 f = unitBallSupportFace 𝕜 (a • g) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    have hempty (l : StrongDual 𝕜 E) : unitBallSupportFace 𝕜 l = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx₀ : x = 0 := Subsingleton.elim _ _
      have hval : l x = 1 := hx.2
      rw [hx₀, map_zero] at hval
      exact zero_ne_one hval
    exact ⟨1, norm_one, by rw [hempty f, hempty (1 • g)]⟩
  · letI := hE
    have hF := hU.isMaximalFace_unitBallSupportFace 𝕜 hf
    obtain ⟨x, hx⟩ := hF.nonempty
    have hxnorm : ‖x‖ = 1 := (show ‖x‖ = 1 by simpa only [Metric.mem_sphere, dist_zero_right] using hF.subset_sphere hx)
    have hxU := hU.unitBallSupportFace_subset 𝕜 hf hx
    have hgxnorm : ‖g x‖ = 1 := (hg x hxU).2.trans hxnorm
    have hgx : g x ≠ 0 := norm_ne_zero_iff.mp (hgxnorm.trans_ne one_ne_zero)
    have ha : ‖(g x)⁻¹‖ = 1 := by rw [norm_inv, hgxnorm, inv_one]
    refine ⟨(g x)⁻¹, ha, ?_⟩
    exact hU.unitBallSupportFace_eq_of_common_apply_eq_one 𝕜 hf
      (fun y hy => smul_mem_absoluteNormingFunctionals 𝕜 ha (hg y hy))
      hxnorm hx.2 (inv_mul_cancel₀ hgx)

/-- A simultaneous version for the entire support family of one maximal
face, with the original union-of-support-kernels identification retained. -/
theorem IsMaximalFace.exists_maximal_filter_forall_supportFunctionals
    {F : Set E} (hF : IsMaximalFace F) :
    ∃ U : Set E, F ⊆ U ∧ IsMaximalBirkhoffJamesFilter 𝕜 U ∧
      (∀ f ∈ supportFunctionals 𝕜 F, ∀ x ∈ U,
        f ∈ absoluteNormingFunctionals 𝕜 x) ∧
      birkhoffJamesKernel 𝕜 U = supportKernelUnion 𝕜 F := by
  obtain ⟨x, hx⟩ := hF.nonempty
  have hxne : x ≠ 0 :=
    norm_ne_zero_iff.mp (((show ‖x‖ = 1 by simpa only [Metric.mem_sphere, dist_zero_right] using hF.subset_sphere hx)).trans_ne one_ne_zero)
  letI : Nontrivial E := ⟨⟨x, 0, hxne⟩⟩
  obtain ⟨U, hFU, hU, hkernel⟩ := hF.exists_isMaximalBirkhoffJamesFilter 𝕜
  exact ⟨U, hFU, hU,
    fun f hf => hF.mem_absoluteNormingFunctionals_of_subset_maximal_filter 𝕜 hU hFU hf,
    hkernel⟩

end NormedSpace
