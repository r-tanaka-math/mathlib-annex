/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

/-!
# Rank-one and finite-rank operators in two-sided ideals

These are ideals of the actual ring of bounded operators. No replacement norm,
star-closedness hypothesis, or scalar-stability hypothesis is imposed on an ideal.
A single nonzero member generates every rank-one operator by two-sided multiplication.
Finite-rank operators are written as finite sums of Mathlib's `rankOne` using an
orthonormal basis of their range. A zero range gives an empty sum.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A rank-one sandwich detects one nonzero value of a bounded operator. -/
theorem rankOne_mul_mul_rankOne (a : H →L[𝕜] H) (x u v : H) :
    (rankOne 𝕜 u (a x) * a) * rankOne 𝕜 x v =
      inner 𝕜 (a x) (a x) • rankOne 𝕜 u v := by
  ext z
  simp only [ContinuousLinearMap.mul_apply, rankOne_apply, map_smul,
    inner_smul_right, ContinuousLinearMap.smul_apply, smul_smul]
  rw [mul_comm]

end InnerProductSpace

namespace TwoSidedIdeal

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Every nonzero algebraic two-sided ideal of bounded operators contains all rank-one
operators. Closedness of the ideal and completeness of the space are not needed. -/
theorem rankOne_mem_of_ne_bot (I : TwoSidedIdeal (H →L[𝕜] H)) (hI : I ≠ ⊥)
    (u v : H) : InnerProductSpace.rankOne 𝕜 u v ∈ I := by
  classical
  obtain ⟨a, ha, ha0⟩ : ∃ a : H →L[𝕜] H, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hI
    ext a
    simp only [TwoSidedIdeal.mem_bot]
    exact ⟨h a, fun h0 => h0 ▸ I.zero_mem⟩
  obtain ⟨x, hx⟩ : ∃ x : H, a x ≠ 0 := by
    by_contra! h
    apply ha0
    ext x
    exact h x
  let c : 𝕜 := inner 𝕜 (a x) (a x)
  have hc : c ≠ 0 := by simpa only [c, ne_eq, inner_self_eq_zero] using hx
  have hs : (InnerProductSpace.rankOne 𝕜 (c⁻¹ • u) (a x) * a) *
      InnerProductSpace.rankOne 𝕜 x v ∈ I :=
    I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)
  have he : (InnerProductSpace.rankOne 𝕜 (c⁻¹ • u) (a x) * a) *
      InnerProductSpace.rankOne 𝕜 x v = InnerProductSpace.rankOne 𝕜 u v := by
    rw [InnerProductSpace.rankOne_mul_mul_rankOne]
    ext z
    simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
      smul_smul]
    change (c * (inner 𝕜 v z * c⁻¹)) • u = inner 𝕜 v z • u
    rw [mul_comm (inner 𝕜 v z) c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  exact he ▸ hs

end TwoSidedIdeal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A bounded finite-rank operator between Hilbert spaces is an actual finite sum of
rank-one operators. Only its range, not the ambient spaces, is finite-dimensional. -/
theorem exists_sum_rankOne_eq_of_finiteDimensional_range (a : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (LinearMap.range a.toLinearMap)] :
    ∃ (n : ℕ) (u : Fin n → F) (v : Fin n → E),
      (∑ i, InnerProductSpace.rankOne 𝕜 (u i) (v i)) = a := by
  classical
  let M : Submodule 𝕜 F := LinearMap.range a.toLinearMap
  let b := stdOrthonormalBasis 𝕜 M
  refine ⟨Module.finrank 𝕜 M, fun i => (b i : F),
    fun i => a.adjoint (b i : F), ?_⟩
  ext x
  have h := congrArg M.subtype (b.sum_repr' ⟨a x, ⟨x, rfl⟩⟩)
  simp only [map_sum, map_smul] at h
  change (∑ i, inner 𝕜 (b i : F) (a x) • (b i : F)) = a x at h
  simpa only [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply,
    ContinuousLinearMap.adjoint_inner_left] using h

end ContinuousLinearMap

namespace TwoSidedIdeal

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A nonzero two-sided ideal contains every bounded finite-rank operator. -/
theorem mem_of_finiteDimensional_range (I : TwoSidedIdeal (H →L[𝕜] H))
    (hI : I ≠ ⊥) (a : H →L[𝕜] H)
    [FiniteDimensional 𝕜 (LinearMap.range a.toLinearMap)] : a ∈ I := by
  classical
  obtain ⟨n, u, v, he⟩ := a.exists_sum_rankOne_eq_of_finiteDimensional_range
  rw [← he]
  exact sum_mem fun i _ => I.rankOne_mem_of_ne_bot hI (u i) (v i)

/-- The full bounded-operator ring on a finite-dimensional Hilbert space is simple.
The zero ideal is retained as a separate branch, including the zero Hilbert space. -/
theorem eq_bot_or_eq_top_of_finiteDimensional (I : TwoSidedIdeal (H →L[𝕜] H))
    [FiniteDimensional 𝕜 H] : I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  apply top_unique
  intro a _
  exact I.mem_of_finiteDimensional_range hI a

end TwoSidedIdeal
