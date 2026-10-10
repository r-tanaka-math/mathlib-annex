/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.Module.BiorthogonalSequence
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.RingTheory.SimpleModule.Basic
public import MathlibAnnex.Analysis.Complex.RingEquiv
import Mathlib.Tactic

/-!
# Semilinear regularity from closed hyperplane images

The scalar automorphism is arbitrary at input. A norm-convergent continuous-dual
series built from a biorthogonal sequence rules out scalar discontinuity. Only
afterwards do Gaussian-rational density and the closed graph theorem enter.
Scalar continuity, the identity/conjugation dichotomy, and continuity of both
vector-space maps are separate results. Images of source hyperplanes are used;
for an inverse-image hypothesis the theorem must be applied to the inverse map.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate


namespace LinearEquiv

universe u v
variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℂ X]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable {σ : ℂ ≃+* ℂ}

local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : ℂ ≃+* ℂ) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- Scalar regularity needs only normed spaces. Its hypothesis is the image
closedness of actual nonzero continuous-functional kernels, not a regularity oracle. -/
theorem continuous_ringEquiv_of_isClosed_image_ker
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hX : ¬ FiniteDimensional ℂ X)
    (hclosed : ∀ f : StrongDual ℂ X, f ≠ 0 →
      IsClosed (T '' (f.ker : Set X))) : Continuous σ := by
  classical
  by_contra hσ
  obtain ⟨x, f, hbio, hnorm⟩ :=
    NormedSpace.exists_biorthogonal_sequence_norm_le_geometric hX
  have hd : ∀ n : ℕ, ∃ d : ℂ,
      ‖d‖ ≤ 1 ∧ (n + 1 : ℝ) * (‖T (x n)‖ + 1) < ‖σ d‖ :=
    fun n => Complex.exists_norm_map_gt_of_not_continuous σ hσ _
  choose d hdunit hdgrowth using hd
  have hdn : ∀ n, d n ≠ 0 := by
    intro n hz
    have h := hdgrowth n
    rw [hz, map_zero, norm_zero] at h
    have hp : (0 : ℝ) < (n + 1 : ℝ) * (‖T (x n)‖ + 1) := by positivity
    exact (not_lt_of_ge hp.le) h
  have hs : Summable (fun n => d n • f n) :=
    NormedSpace.summable_smul_of_norm_le_geometric f hnorm d hdunit
  let F : StrongDual ℂ X := ∑' n, d n • f n
  have hFx : ∀ n, F (x n) = d n :=
    NormedSpace.tsum_smul_apply_of_biorthogonal x f hbio d hs
  have hF : F ≠ 0 := by
    intro hz
    exact hdn 0 (by simpa [hz] using (hFx 0).symm)
  have hFl : F.toLinearMap ≠ 0 := by
    intro hz
    apply hF
    ext z
    exact congrArg (fun g : X →ₗ[ℂ] ℂ => g z) hz
  obtain ⟨x₀, hx₀⟩ := (LinearMap.surjective_iff_ne_zero.2 hFl) 1
  change F x₀ = 1 at hx₀
  let y : ℕ → X := fun n => x₀ - (d n)⁻¹ • x n
  have hy : ∀ n, y n ∈ F.ker := by
    intro n
    change F (x₀ - (d n)⁻¹ • x n) = 0
    rw [map_sub, F.map_smul, hx₀, hFx, smul_eq_mul, inv_mul_cancel₀ (hdn n), sub_self]
  have hdist : ∀ n, dist (T (y n)) (T x₀) ≤ 1 / (n + 1 : ℝ) := by
    intro n
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hdpos : 0 < ‖σ (d n)‖ :=
      lt_trans (by positivity) (hdgrowth n)
    have heq : dist (T (y n)) (T x₀) = ‖T (x n)‖ / ‖σ (d n)‖ := by
      rw [dist_eq_norm, show T (y n) = T x₀ - σ ((d n)⁻¹) • T (x n) by
        simp only [y, map_sub, map_smulₛₗ]
        rfl]
      rw [sub_sub_cancel_left, norm_neg, norm_smul, map_inv₀, norm_inv, div_eq_mul_inv,
        mul_comm]
    rw [heq]
    apply (div_le_iff₀ hdpos).2
    have hg : ‖T (x n)‖ * (n + 1) ≤ ‖σ (d n)‖ := by
      nlinarith [hdgrowth n]
    calc
      ‖T (x n)‖ ≤ ‖σ (d n)‖ / (n + 1) := (le_div_iff₀ hn).2 hg
      _ = 1 / (n + 1) * ‖σ (d n)‖ := by ring
  have ht : Tendsto (fun n => T (y n)) atTop (𝓝 (T x₀)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) hdist
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hm : T x₀ ∈ T '' (F.ker : Set X) :=
    (hclosed F hF).mem_of_tendsto ht (Eventually.of_forall fun n => ⟨y n, hy n, rfl⟩)
  obtain ⟨z, hz, heq⟩ := hm
  have hz₀ : z = x₀ := T.injective heq
  have : F x₀ = 0 := by
    change F z = 0 at hz
    simpa only [hz₀] using hz
  exact one_ne_zero (hx₀.symm.trans this)

/-- Literal closed-hyperplane formulation. `IsCoatom` is codimension one in
 the algebraic submodule lattice; the norm closedness is a separate hypothesis. -/
theorem continuous_ringEquiv_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hX : ¬ FiniteDimensional ℂ X)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) : Continuous σ := by
  apply continuous_ringEquiv_of_isClosed_image_ker T hX
  intro f hf
  have hfl : f.toLinearMap ≠ 0 := by
    intro hz
    apply hf
    ext x
    exact congrArg (fun g : X →ₗ[ℂ] ℂ => g x) hz
  exact hclosed f.ker
    (LinearMap.isCoatom_ker_of_surjective (LinearMap.surjective_iff_ne_zero.2 hfl))
    f.isClosed_ker

/-- The scalar automorphism dichotomy under the original image condition. -/
theorem ringEquiv_eq_refl_or_conj_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hX : ¬ FiniteDimensional ℂ X)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) :
    σ = RingEquiv.refl ℂ ∨ σ = starRingAut (R := ℂ) :=
  Complex.ringEquiv_eq_refl_or_conj_of_continuous σ
    (continuous_ringEquiv_of_isClosed_image_hyperplane T hX hclosed)


/-- A continuous scalar automorphism fixes the real field, so the same actual
semilinear bijection becomes a real-linear equivalence. This construction has no
continuity field for the vector-space map. -/
def realLinearEquivOfContinuousRingEquiv
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hσ : Continuous σ) : X ≃ₗ[ℝ] Y where
  toFun := T
  invFun := T.symm
  left_inv := T.symm_apply_apply
  right_inv := T.apply_symm_apply
  map_add' := T.map_add
  map_smul' r x := by
    change T ((r : ℂ) • x) = (r : ℂ) • T x
    rw [map_smulₛₗ]
    change σ (r : ℂ) • T x = (r : ℂ) • T x
    rw [Complex.ringEquiv_apply_ofReal_of_continuous σ hσ]

/-- Transporting an actual continuous dual functional across the inverse map
and then applying σ is complex linear, even before vector-space continuity. -/
def transportedDualLinearMap (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y)
    (f : StrongDual ℂ X) : Y →ₗ[ℂ] ℂ where
  toFun y := σ (f (T.symm y))
  map_add' y z := by simp only [map_add]
  map_smul' c y := by
    change σ (f (T.symm (c • y))) = c • σ (f (T.symm y))
    rw [T.symm.map_smulₛₗ, f.map_smul, smul_eq_mul, σ.map_mul, smul_eq_mul]
    change σ (σ.symm c) * σ (f (T.symm y)) = c * σ (f (T.symm y))
    rw [σ.apply_symm_apply]

/-- The transported scalar functional has precisely the image kernel, not the
preimage kernel. This is the orientation used in the regularity hypothesis. -/
theorem ker_transportedDualLinearMap (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y)
    (f : StrongDual ℂ X) :
    ((transportedDualLinearMap T f).ker : Set Y) = T '' (f.ker : Set X) := by
  ext y
  constructor
  · intro hy
    change σ (f (T.symm y)) = 0 at hy
    have hz : f (T.symm y) = 0 := σ.injective (by
      simpa only [map_zero] using hy)
    exact ⟨T.symm y, hz, T.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    change σ (f (T.symm (T x))) = 0
    rw [T.symm_apply_apply, show f x = 0 from hx, map_zero]

/-- Closed image hyperplanes imply continuity of each transported functional.
No continuity of T or its inverse is used here. -/
theorem continuous_transportedDualLinearMap
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) (f : StrongDual ℂ X) :
    Continuous (transportedDualLinearMap T f) := by
  apply (transportedDualLinearMap T f).continuous_iff_isClosed_ker.2
  rw [ker_transportedDualLinearMap]
  by_cases hf : f = 0
  · subst f
    have heq : T '' ((0 : StrongDual ℂ X).ker : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; trivial
      · intro _
        exact ⟨T.symm y, by simp, T.apply_symm_apply y⟩
    rw [heq]
    exact isClosed_univ
  · have hfl : f.toLinearMap ≠ 0 := by
      intro hz
      apply hf
      ext x
      exact congrArg (fun g : X →ₗ[ℂ] ℂ => g x) hz
    exact hclosed f.ker
      (LinearMap.isCoatom_ker_of_surjective (LinearMap.surjective_iff_ne_zero.2 hfl))
      f.isClosed_ker

/-- Literal linear or conjugate-linear alternatives for the same function T. -/
theorem map_smul_or_map_conj_smul_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hX : ¬ FiniteDimensional ℂ X)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) :
    (∀ c : ℂ, ∀ x : X, T (c • x) = c • T x) ∨
      (∀ c : ℂ, ∀ x : X, T (c • x) = conj c • T x) := by
  rcases ringEquiv_eq_refl_or_conj_of_isClosed_image_hyperplane T hX hclosed with h | h
  · left
    intro c x
    rw [T.map_smulₛₗ]
    change σ c • T x = c • T x
    have hc : σ c = c := by rw [h]; rfl
    rw [hc]
  · right
    intro c x
    rw [T.map_smulₛₗ]
    change σ c • T x = conj c • T x
    have hc : σ c = conj c := by rw [h]; rfl
    rw [hc]

variable [CompleteSpace X] [CompleteSpace Y]

/-- Boundedness is a second argument after scalar regularity. The closed graph
of the inverse is detected by the transported continuous dual, then the Banach
inverse theorem gives continuity of the forward map. -/
theorem continuous_and_continuous_symm_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hσ : Continuous σ)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) : Continuous T ∧ Continuous T.symm := by
  let R := realLinearEquivOfContinuousRingEquiv T hσ
  have hR : Continuous R.symm := by
    apply R.symm.toLinearMap.continuous_of_seq_closed_graph
    intro u y x hu hx
    change x = T.symm y
    by_contra hxy
    obtain ⟨f, hfn, hfv⟩ := exists_dual_vector ℂ (x - T.symm y)
      (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy))
    have hx' : Tendsto (fun n => T.symm (u n)) atTop (𝓝 x) := hx
    have h₁ : Tendsto (fun n => σ (f (T.symm (u n)))) atTop (𝓝 (σ (f x))) :=
      (hσ.continuousAt.tendsto).comp ((f.continuous.continuousAt.tendsto).comp hx')
    have h₂ : Tendsto (fun n => σ (f (T.symm (u n)))) atTop
        (𝓝 (σ (f (T.symm y)))) :=
      (continuous_transportedDualLinearMap T hclosed f).continuousAt.tendsto.comp hu
    have hval : f x = f (T.symm y) := σ.injective (tendsto_nhds_unique h₁ h₂)
    have hfzero : f (x - T.symm y) = 0 := by rw [map_sub, hval, sub_self]
    have hz : (‖x - T.symm y‖ : ℂ) = 0 := hfv.symm.trans hfzero
    have hn : ‖x - T.symm y‖ = 0 := by exact_mod_cast hz
    exact hxy (sub_eq_zero.1 (norm_eq_zero.1 hn))
  have hRf : Continuous R := by
    simpa only [LinearEquiv.symm_symm] using R.symm.continuous_symm hR
  exact ⟨hRf, hR⟩

/-- Explicit norm bounds for both actual functions after scalar regularity.
Positive constants are supplied; no boundedness hypothesis has been inserted. -/
theorem exists_bounds_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hσ : Continuous σ)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      (∀ x, ‖T x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖T.symm y‖ ≤ D * ‖y‖) := by
  let R := realLinearEquivOfContinuousRingEquiv T hσ
  have ht := continuous_and_continuous_symm_of_isClosed_image_hyperplane T hσ hclosed
  let U : X ≃L[ℝ] Y := R.toContinuousLinearEquivOfContinuous ht.1
  refine ⟨‖U.toContinuousLinearMap‖ + 1, ‖U.symm.toContinuousLinearMap‖ + 1,
    by positivity, by positivity, ?_, ?_⟩
  · intro x
    exact (U.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
  · intro y
    exact (U.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg y))

/-- Closed hyperplane images force both scalar regularity and bounded invertibility.
Infinite dimensionality is only required of the source; no separability is used. -/
theorem regularity_of_isClosed_image_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hX : ¬ FiniteDimensional ℂ X)
    (hclosed : ∀ M : Submodule ℂ X, IsCoatom M → IsClosed (M : Set X) →
      IsClosed (T '' (M : Set X))) :
    (σ = RingEquiv.refl ℂ ∨ σ = starRingAut (R := ℂ)) ∧
      Continuous T ∧ Continuous T.symm ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
        (∀ x, ‖T x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖T.symm y‖ ≤ D * ‖y‖) := by
  have hs := continuous_ringEquiv_of_isClosed_image_hyperplane T hX hclosed
  have ht := continuous_and_continuous_symm_of_isClosed_image_hyperplane T hs hclosed
  exact ⟨Complex.ringEquiv_eq_refl_or_conj_of_continuous σ hs, ht.1, ht.2,
    exists_bounds_of_isClosed_image_hyperplane T hs hclosed⟩

/-- Adapter for the inverse-image orientation supplied by the normal-part
closed-subspace theorem. The forward-image theorem is applied to T inverse. -/
theorem continuous_and_continuous_symm_of_isClosed_preimage_hyperplane
    (T : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) X Y) (hY : ¬ FiniteDimensional ℂ Y)
    (hclosed : ∀ N : Submodule ℂ Y, IsCoatom N → IsClosed (N : Set Y) →
      IsClosed (T ⁻¹' (N : Set Y))) : Continuous T ∧ Continuous T.symm := by
  have hi : ∀ N : Submodule ℂ Y, IsCoatom N → IsClosed (N : Set Y) →
      IsClosed (T.symm '' (N : Set Y)) := by
    intro N hN hc
    have heq : T.symm '' (N : Set Y) = T ⁻¹' (N : Set Y) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa only [Set.mem_preimage, T.apply_symm_apply] using hy
      · intro hx
        exact ⟨T x, hx, T.symm_apply_apply x⟩
    rw [heq]
    exact hclosed N hN hc
  have hs := continuous_ringEquiv_of_isClosed_image_hyperplane (σ := σ.symm) T.symm hY hi
  have ht := continuous_and_continuous_symm_of_isClosed_image_hyperplane (σ := σ.symm) T.symm hs hi
  exact ⟨ht.2, ht.1⟩

end LinearEquiv
