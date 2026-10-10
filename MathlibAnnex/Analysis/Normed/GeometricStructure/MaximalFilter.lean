/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.FaceKernel

/-!
# Maximal orthogonality filters and maximal faces

A maximal filter is the full absolute norm-attainment set of any common
absolute support. In a nontrivial normed space this support has norm one and
its value-one face is maximal. This proof uses the actual norm-attainment
filter constructed earlier, rather than a uniqueness assumption for supports.
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

theorem IsMaximalBirkhoffJamesFilter.eq_absoluteNormAttainmentSet {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f : StrongDual 𝕜 E}
    (hf : ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) :
    U = absoluteNormAttainmentSet 𝕜 f := by
  obtain ⟨x₀, hx₀⟩ := hU.1.nonempty 𝕜
  have hsub : U ⊆ absoluteNormAttainmentSet 𝕜 f := fun x hx => (hf x hx).2
  exact Subset.antisymm hsub
    (hU.2 (isBirkhoffJamesFilter_absoluteNormAttainmentSet 𝕜 (hf x₀ hx₀).1) hsub)

variable [Nontrivial E]

/-- A maximal filter in a nontrivial normed space cannot consist only of zero. -/
theorem IsMaximalBirkhoffJamesFilter.exists_ne_zero {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) : ∃ x ∈ U, x ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ x ∈ U, x = 0 := by
    intro x hx
    by_contra hx₀
    exact h ⟨x, hx, hx₀⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have hp : IsBirkhoffJamesFilter 𝕜 (birkhoffJamesUpperClosure 𝕜 {y}) :=
    isBirkhoffJamesFilter_upperClosure 𝕜 (singleton_nonempty y) (by
      intro x hx z hz
      have hx' : x = y := mem_singleton_iff.mp hx
      have hz' : z = y := mem_singleton_iff.mp hz
      subst x
      subst z
      exact ⟨y, mem_singleton y, Subset.rfl, Subset.rfl⟩)
  have hsub : U ⊆ birkhoffJamesUpperClosure 𝕜 {y} := by
    intro x hx
    rw [hzero x hx]
    exact hp.zero_mem 𝕜
  have hyU : y ∈ U := hU.2 hp hsub (subset_birkhoffJamesUpperClosure 𝕜 {y} (mem_singleton y))
  exact hy (hzero y hyU)

theorem IsMaximalBirkhoffJamesFilter.norm_eq_one {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f : StrongDual 𝕜 E}
    (hf : ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) : ‖f‖ = 1 := by
  obtain ⟨x, hx, hx₀⟩ := hU.exists_ne_zero 𝕜
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx₀
  have hle : ‖x‖ ≤ ‖f‖ * ‖x‖ := (hf x hx).2 ▸ f.le_opNorm x
  exact le_antisymm (hf x hx).1 ((mul_le_mul_iff_left₀ hxpos).mp
    (by simpa only [one_mul] using hle))

/-- A common absolute support of a maximal filter exposes an actual maximal
face of the primal ball. -/
theorem IsMaximalBirkhoffJamesFilter.isMaximalFace_unitBallSupportFace {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f : StrongDual 𝕜 E}
    (hf : ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) :
    IsMaximalFace (unitBallSupportFace 𝕜 f) := by
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hU.exists_ne_zero 𝕜
  have hfnorm : ‖f‖ ≤ 1 := (hf x₀ hx₀).1
  let u : E := (f x₀)⁻¹ • x₀
  have hu : u ∈ unitBallSupportFace 𝕜 f := inv_apply_smul_mem_unitBallSupportFace 𝕜 (hf x₀ hx₀) hx₀ne
  apply isMaximalFace_of_maximal_convex_subset_sphere ⟨u, hu⟩
  refine ⟨⟨convex_unitBallSupportFace 𝕜 f, unitBallSupportFace_subset_sphere 𝕜 hfnorm⟩, ?_⟩
  intro G hG hFG
  obtain ⟨g, hg⟩ := nonempty_supportFunctionals_of_convex_subset_sphere 𝕜
    ⟨u, hFG hu⟩ hG.1 hG.2
  have hUg : U ⊆ absoluteNormAttainmentSet 𝕜 g := by
    intro x hx
    by_cases hx₀ : x = 0
    · subst x
      simp [absoluteNormAttainmentSet]
    have hfx : f x ≠ 0 := norm_ne_zero_iff.mp ((hf x hx).2.trans_ne (norm_ne_zero_iff.mpr hx₀))
    have hvalue : (f x)⁻¹ * g x = 1 := by
      simpa only [map_smul, smul_eq_mul] using hg.2 ((f x)⁻¹ • x)
        (hFG (inv_apply_smul_mem_unitBallSupportFace 𝕜 (hf x hx) hx₀))
    have heq : g x = f x := by
      calc
        g x = f x * ((f x)⁻¹ * g x) := by rw [← mul_assoc, mul_inv_cancel₀ hfx, one_mul]
        _ = f x := by rw [hvalue, mul_one]
    change ‖g x‖ = ‖x‖
    rw [heq, (hf x hx).2]
  have hGnorm : ∀ x ∈ G, ‖x‖ = 1 := fun x hx => by
    simpa only [Metric.mem_sphere, dist_zero_right] using hG.2 hx
  have hGU : G ⊆ U := by
    intro x hx
    apply hU.2 (isBirkhoffJamesFilter_absoluteNormAttainmentSet 𝕜 hg.1) hUg
    change ‖g x‖ = ‖x‖
    rw [hg.2 x hx, norm_one, hGnorm x hx]
  have hfone : ∀ x ∈ G, f x = 1 := eq_one_on_convex_of_norm_apply_eq_one 𝕜 hG.1
    (fun x hx => (hf x (hGU hx)).2.trans (hGnorm x hx)) (hFG hu) hu.2
  intro x hx
  exact ⟨mem_closedBall_zero_iff.mpr (hGnorm x hx).le, hfone x hx⟩

/-- The filter kernel is the original union-of-support-kernels of its face. -/
theorem IsMaximalBirkhoffJamesFilter.kernel_eq_supportKernelUnion {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) {f : StrongDual 𝕜 E}
    (hf : ∀ x ∈ U, f ∈ absoluteNormingFunctionals 𝕜 x) :
    birkhoffJamesKernel 𝕜 U = supportKernelUnion 𝕜 (unitBallSupportFace 𝕜 f) := by
  have hface := hU.isMaximalFace_unitBallSupportFace 𝕜 hf
  rw [hU.eq_absoluteNormAttainmentSet 𝕜 hf,
    birkhoffJamesKernel_absoluteNormAttainmentSet 𝕜 (hU.norm_eq_one 𝕜 hf).le]
  exact birkhoffJamesKernel_eq_supportKernelUnion 𝕜 hface.nonempty hface.convex hface.subset_sphere

/-- Every maximal face has a maximal-filter presentation. The proof rotates
one common absolute support of a containing maximal filter; it does not
assume uniqueness of the face's supports. -/
theorem IsMaximalFace.exists_isMaximalBirkhoffJamesFilter {F : Set E} (hF : IsMaximalFace F) :
    ∃ U : Set E, F ⊆ U ∧ IsMaximalBirkhoffJamesFilter 𝕜 U ∧
      birkhoffJamesKernel 𝕜 U = supportKernelUnion 𝕜 F := by
  obtain ⟨U, hFU, hU⟩ := exists_isMaximalBirkhoffJamesFilter_of_directed 𝕜 hF.nonempty
    (directed_birkhoffJamesOrthogonalSet_of_convex_subset_sphere 𝕜 hF.convex hF.subset_sphere)
  obtain ⟨f, hf⟩ := hU.1.exists_common_absoluteNormingFunctional 𝕜
  obtain ⟨a, ha, haf⟩ := exists_norm_eq_one_smul_mem_supportFunctionals 𝕜 hF.nonempty hF.convex
    hF.subset_sphere (fun x hx => hf x (hFU hx))
  have hag : ∀ x ∈ U, a • f ∈ absoluteNormingFunctionals 𝕜 x := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa only [norm_smul, ha, one_mul] using (hf x hx).1
    · change ‖a * f x‖ = ‖x‖
      rw [norm_mul, ha, one_mul, (hf x hx).2]
  refine ⟨U, hFU, hU, ?_⟩
  rw [hF.eq_unitBallSupportFace 𝕜 haf]
  exact hU.kernel_eq_supportKernelUnion 𝕜 hag

end NormedSpace
