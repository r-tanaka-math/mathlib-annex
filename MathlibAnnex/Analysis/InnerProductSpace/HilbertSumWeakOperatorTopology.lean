/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumCoordinates
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic

/-!
# Finite block-diagonal operators with the weak operator topology

The product of the actual weak-operator spaces on a finite dependent family
is homeomorphic to the closed block-diagonal subset of the ambient
weak-operator space on `HilbertSum`. Neither the fibers nor their sum are
assumed separable or finite dimensional. Empty index sets and zero fibers
are allowed. The bound used to construct a diagonal operator is not used as
a topology on the domain: that domain has the product weak operator topology.
-/

set_option autoImplicit false
noncomputable section
open Set Topology
open scoped ENNReal lp

namespace MathlibAnnex.Analysis.InnerProductSpace

universe u v
variable {I : Type u} [Fintype I] [DecidableEq I] {H : I → Type v}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- The finite diagonal map from the product weak operator topology to the
ambient weak operator topology. The finite norm sum only constructs a CLM. -/
def diagonalWOT (T : ∀ i, H i →WOT[ℂ] H i) :
    HilbertSum H →WOT[ℂ] HilbertSum H :=
  ContinuousLinearMapWOT.ofCLM <| diagonal (fun i => (T i).toCLM)
    (∑ i, ‖(T i).toCLM‖) (Finset.sum_nonneg fun i _ => norm_nonneg (T i).toCLM)
    (fun i => Finset.single_le_sum (fun j _ => norm_nonneg (T j).toCLM) (Finset.mem_univ i))

@[simp]
theorem diagonalWOT_apply (T : ∀ i, H i →WOT[ℂ] H i) (x : HilbertSum H) (i : I) :
    diagonalWOT T x i = T i (x i) := rfl

/-- Bounded diagonal operators do not depend on the chosen bound when
regarded in the weak operator space. -/
theorem diagonalWOT_ofCLM (T : ∀ i, H i →L[ℂ] H i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) :
    diagonalWOT (fun i => ContinuousLinearMapWOT.ofCLM (T i)) =
      ContinuousLinearMapWOT.ofCLM (diagonal T C hC hT) := by
  apply ContinuousLinearMapWOT.ext
  intro x
  apply lp.ext
  funext i
  rfl

/-- The diagonal blocks of an ambient operator, recovered by the actual
bounded coordinate inclusion and projection. -/
def coordinateWOT (T : HilbertSum H →WOT[ℂ] HilbertSum H) :
    ∀ i, H i →WOT[ℂ] H i :=
  fun i => ContinuousLinearMapWOT.ofCLM
    ((coordinateProjection i).comp (T.toCLM.comp (coordinateEmbedding i)))

@[simp]
theorem coordinateWOT_apply (T : HilbertSum H →WOT[ℂ] HilbertSum H)
    (i : I) (x : H i) :
    coordinateWOT T i x = T (coordinateEmbedding i x) i := rfl

@[simp]
theorem coordinateWOT_diagonalWOT (T : ∀ i, H i →WOT[ℂ] H i) :
    coordinateWOT (diagonalWOT T) = T := by
  funext i
  apply ContinuousLinearMapWOT.ext
  intro x
  simp [coordinateEmbedding_apply, lp.coeFn_single]

theorem diagonalWOT_injective : Function.Injective (diagonalWOT (H := H)) := by
  intro T S h
  simpa only [coordinateWOT_diagonalWOT] using congrArg coordinateWOT h

/-- Every matrix coefficient of the diagonal map is a finite sum of
coordinate matrix coefficients. -/
theorem inner_diagonalWOT (T : ∀ i, H i →WOT[ℂ] H i) (x y : HilbertSum H) :
    inner ℂ y (diagonalWOT T x) = ∑ i, inner ℂ (y i) (T i (x i)) := by
  simp only [lp.inner_eq_tsum, tsum_fintype, diagonalWOT_apply]

/-- Forward continuity uses finite scalar sums, not strong continuity of
operator evaluation or of taking adjoints. -/
theorem continuous_diagonalWOT : Continuous (diagonalWOT (H := H)) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  simp_rw [inner_diagonalWOT]
  have hi (i : I) : Continuous
      (fun T : ∀ i, H i →WOT[ℂ] H i => inner ℂ (y i) (T i (x i))) :=
    (ContinuousLinearMapWOT.continuous_dual_apply (x i) (innerSL ℂ (y i))).comp
      (continuous_apply i)
  fun_prop

/-- Inverse coordinate recovery is continuous on the entire ambient space,
not merely on the block-diagonal range. -/
theorem continuous_coordinateWOT : Continuous (coordinateWOT (H := H)) := by
  apply continuous_pi
  intro i
  exact (ContinuousLinearMapWOT.continuous_postcomp
    (ContinuousLinearMapWOT.ofCLM (coordinateProjection (H := H) i))).comp
    (ContinuousLinearMapWOT.continuous_precomp
      (ContinuousLinearMapWOT.ofCLM (coordinateEmbedding (H := H) i)))

/-- The block-diagonal set, defined by vanishing off-diagonal blocks. -/
def blockDiagonalWOT : Set (HilbertSum H →WOT[ℂ] HilbertSum H) :=
  {T | ∀ i j, i ≠ j → ∀ x : H j, T (coordinateEmbedding j x) i = 0}

theorem diagonalWOT_mem_blockDiagonalWOT (T : ∀ i, H i →WOT[ℂ] H i) :
    diagonalWOT T ∈ blockDiagonalWOT (H := H) := by
  intro i j hij x
  simp [coordinateEmbedding_apply, lp.coeFn_single, hij, hij.symm]

/-- Off-diagonal vanishing gives exact reconstruction. The proof uses the
finite expansion of a vector in the genuine dependent Hilbert sum. -/
theorem diagonalWOT_coordinateWOT {T : HilbertSum H →WOT[ℂ] HilbertSum H}
    (hT : T ∈ blockDiagonalWOT (H := H)) : diagonalWOT (coordinateWOT T) = T := by
  apply ContinuousLinearMapWOT.ext
  intro x
  have hxsum : x = ∑ j : I, coordinateEmbedding j (x j) := by
    have hs : HasSum (fun j : I => coordinateEmbedding j (x j)) x := by
      simpa only [coordinateEmbedding_apply] using
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x)
    exact hs.unique (hasSum_fintype _)
  apply lp.ext
  funext i
  calc
    diagonalWOT (coordinateWOT T) x i = T (coordinateEmbedding i (x i)) i := rfl
    _ = ∑ j : I, T (coordinateEmbedding j (x j)) i := by
      symm
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hT i j hji.symm (x j)
      · simp
    _ = T (∑ j : I, coordinateEmbedding j (x j)) i := by
      rw [map_sum]
      exact (map_sum (coordinateProjection i)
        (fun j : I => T (coordinateEmbedding j (x j))) Finset.univ).symm
    _ = T x i := by rw [← hxsum]

/-- The range is exactly the block-diagonal set, in both directions. -/
theorem range_diagonalWOT : Set.range (diagonalWOT (H := H)) = blockDiagonalWOT := by
  ext T
  constructor
  · rintro ⟨S, rfl⟩
    exact diagonalWOT_mem_blockDiagonalWOT S
  · intro hT
    exact ⟨coordinateWOT T, diagonalWOT_coordinateWOT hT⟩

/-- The range is closed because it is the fixed set of the continuous
retraction obtained by extracting and rebuilding the diagonal blocks. -/
theorem isClosed_range_diagonalWOT : IsClosed (Set.range (diagonalWOT (H := H))) := by
  have heq : Set.range (diagonalWOT (H := H)) =
      {T | diagonalWOT (coordinateWOT T) = T} := by
    ext T
    constructor
    · rintro ⟨S, rfl⟩
      change diagonalWOT (coordinateWOT (diagonalWOT S)) = diagonalWOT S
      rw [coordinateWOT_diagonalWOT]
    · intro hT
      exact ⟨coordinateWOT T, hT⟩
  rw [heq]
  exact isClosed_eq (continuous_diagonalWOT.comp continuous_coordinateWOT) continuous_id

theorem isClosed_blockDiagonalWOT : IsClosed (blockDiagonalWOT (H := H)) := by
  rw [← range_diagonalWOT]
  exact isClosed_range_diagonalWOT

/-- The finite diagonal map is a closed topological embedding. -/
theorem isClosedEmbedding_diagonalWOT : IsClosedEmbedding (diagonalWOT (H := H)) where
  toIsEmbedding :=
    (show Function.LeftInverse coordinateWOT (diagonalWOT (H := H)) from
      coordinateWOT_diagonalWOT).isEmbedding continuous_coordinateWOT continuous_diagonalWOT
  isClosed_range := isClosed_range_diagonalWOT

/-- Explicit homeomorphism with the block-diagonal subspace, with actual
coordinate recovery as inverse. -/
def diagonalWOTHomeomorph : (∀ i, H i →WOT[ℂ] H i) ≃ₜ blockDiagonalWOT (H := H) where
  toFun T := ⟨diagonalWOT T, diagonalWOT_mem_blockDiagonalWOT T⟩
  invFun T := coordinateWOT T.val
  left_inv := coordinateWOT_diagonalWOT
  right_inv T := Subtype.ext (diagonalWOT_coordinateWOT T.property)
  continuous_toFun := continuous_diagonalWOT.subtype_mk _
  continuous_invFun := continuous_coordinateWOT.comp continuous_subtype_val

end MathlibAnnex.Analysis.InnerProductSpace
