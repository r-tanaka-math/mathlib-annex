/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# A bounded-below restriction as a continuous equivalence onto its closed image

These four declarations preserve the author's Hilbert-space hypotheses and exact
functions. They are independent of cardinal-compactness and Rellich theory.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bornology
open scoped Cardinal Topology

universe uF uH uK uI uA
namespace ContinuousLinearMap

section ImageEquivalence

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [hH : CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [hK : CompleteSpace K]

include hH hK in
/-- The restriction to a closed subspace with a positive lower bound, as a
continuous linear equivalence onto its closed literal image. -/
def equivImageOfClosedSubmoduleLowerBound
    (T : H →L[𝕜] K) (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    (hTS : IsClosed (T '' (S : Set H))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖) :
    S ≃L[𝕜] (S.map T.toLinearMap) := by
  letI : CompleteSpace S := hS.completeSpace_coe
  have him : IsClosed (S.map T.toLinearMap : Set K) := hTS
  letI : CompleteSpace (S.map T.toLinearMap) := him.completeSpace_coe
  let q₀ : S →ₗ[𝕜] (S.map T.toLinearMap) :=
    { toFun := fun x => ⟨T x, x, x.property, rfl⟩
      map_add' := by intro x y; apply Subtype.ext; exact map_add T (x : H) (y : H)
      map_smul' := by intro c x; apply Subtype.ext; exact map_smul T c (x : H) }
  let q : S →L[𝕜] (S.map T.toLinearMap) :=
    q₀.mkContinuous ‖T‖ (fun x => T.le_opNorm x)
  have hi : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    have hval : T (x : H) = T (y : H) := congrArg Subtype.val hxy
    have hz : T ((x : H) - (y : H)) = 0 := by
      simp only [map_sub, hval, sub_self]
    have hl := hlower ((x : H) - (y : H)) (S.sub_mem x.property y.property)
    rw [hz, norm_zero] at hl
    have hn : ‖(x : H) - (y : H)‖ = 0 := by
      nlinarith [norm_nonneg ((x : H) - (y : H))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hs : Function.Surjective q := by
    intro y
    obtain ⟨x, hxS, hxy⟩ := y.property
    exact ⟨⟨x, hxS⟩, Subtype.ext hxy⟩
  exact (LinearEquiv.ofBijective q.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquivOfContinuous
    (by exact q.continuous)

/-- The equivalence has exactly the original restriction as its forward function. -/
@[simp]
theorem equivImageOfClosedSubmoduleLowerBound_apply
    (T : H →L[𝕜] K) (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    (hTS : IsClosed (T '' (S : Set H))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖) (x : S) :
    (T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower x : K) = T x := rfl

/-- The inverse is an actual preimage, not a postulated bounded lifting. -/
theorem equivImageOfClosedSubmoduleLowerBound_symm_apply
    (T : H →L[𝕜] K) (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    (hTS : IsClosed (T '' (S : Set H))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖) (y : S.map T.toLinearMap) :
    T ((T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower).symm y : H) =
      (y : K) := by
  let e := T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower
  exact congrArg Subtype.val (e.apply_symm_apply y)

/-- The same lower bound gives the inverse's norm estimate, including the zero space. -/
theorem norm_equivImageOfClosedSubmoduleLowerBound_symm_apply_le
    (T : H →L[𝕜] K) (S : Submodule 𝕜 H) (hS : IsClosed (S : Set H))
    (hTS : IsClosed (T '' (S : Set H))) {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ x ∈ S, δ * ‖x‖ ≤ ‖T x‖) (y : S.map T.toLinearMap) :
    ‖(T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower).symm y‖ ≤
      δ⁻¹ * ‖y‖ := by
  let e := T.equivImageOfClosedSubmoduleLowerBound S hS hTS hδ hlower
  have hl := hlower (e.symm y) (e.symm y).property
  have he : T (e.symm y : H) = (y : K) :=
    T.equivImageOfClosedSubmoduleLowerBound_symm_apply S hS hTS hδ hlower y
  rw [he] at hl
  change ‖(e.symm y : H)‖ ≤ δ⁻¹ * ‖(y : K)‖
  rw [inv_mul_eq_div, le_div_iff₀ hδ]
  simpa only [mul_comm] using hl

end ImageEquivalence

end ContinuousLinearMap
