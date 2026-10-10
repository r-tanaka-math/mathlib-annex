/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FunctionalCoefficient
import Mathlib.Tactic

/-!
# Pointwise ideals for coefficient realizations

Pointwise ideals in bounded sequences and in the auxiliary two-by-two
matrix algebra used by coefficient realizations.  This module records the
actual ideal annihilated by the auxiliary state and is independent of the
later Hahn--Banach and pure-state separation argument.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped CStarAlgebra ComplexOrder InnerProduct BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

section PointwiseIdeals

variable {D : Type u} [CStarAlgebra D]

local instance sequenceOrder : PartialOrder (ℕ →ᵇ D) := CStarAlgebra.spectralOrder _
local instance sequenceStarOrder : StarOrderedRing (ℕ →ᵇ D) :=
  CStarAlgebra.spectralOrderedRing _

/-- Bounded sequences taking every value in a fixed two-sided ideal. -/
def boundedSequenceIdeal (J : TwoSidedIdeal D) : TwoSidedIdeal (ℕ →ᵇ D) :=
  TwoSidedIdeal.mk'
    {x | ∀ n, x n ∈ J}
    (fun _ => J.zero_mem)
    (fun {x y} hx hy n => J.add_mem (hx n) (hy n))
    (fun {x} hx n => J.neg_mem (hx n))
    (fun {x y} hy n => J.mul_mem_left (x n) (y n) (hy n))
    (fun {x y} hx n => J.mul_mem_right (x n) (y n) (hx n))

@[simp]
theorem mem_boundedSequenceIdeal_iff (J : TwoSidedIdeal D) (x : ℕ →ᵇ D) :
    x ∈ boundedSequenceIdeal J ↔ ∀ n, x n ∈ J := by
  simp only [boundedSequenceIdeal, TwoSidedIdeal.mem_mk', Set.mem_setOf_eq]

/-- Two-by-two matrices whose four bounded-sequence entries are pointwise in
`J`.  This is the actual ideal annihilated by the auxiliary coefficient state. -/
def auxiliaryMatrixIdeal (J : TwoSidedIdeal D) :
    TwoSidedIdeal (MathlibAnnex.FunctionalCoefficient.AuxiliaryMatrixAlgebra D) :=
  TwoSidedIdeal.mk'
    {M | ∀ i j, M i j ∈ boundedSequenceIdeal J}
    (fun _ _ => by simp only [mem_boundedSequenceIdeal_iff]; intro; exact J.zero_mem)
    (fun {M N} hM hN i j =>
      (boundedSequenceIdeal J).add_mem (hM i j) (hN i j))
    (fun {M} hM i j => (boundedSequenceIdeal J).neg_mem (hM i j))
    (fun {M N} hN i j => by
      simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
      exact (boundedSequenceIdeal J).add_mem
        ((boundedSequenceIdeal J).mul_mem_left (M i 0) (N 0 j) (hN 0 j))
        ((boundedSequenceIdeal J).mul_mem_left (M i 1) (N 1 j) (hN 1 j)))
    (fun {M N} hM i j => by
      simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
      exact (boundedSequenceIdeal J).add_mem
        ((boundedSequenceIdeal J).mul_mem_right (M i 0) (N 0 j) (hM i 0))
        ((boundedSequenceIdeal J).mul_mem_right (M i 1) (N 1 j) (hM i 1)))

@[simp]
theorem mem_auxiliaryMatrixIdeal_iff (J : TwoSidedIdeal D)
    (M : MathlibAnnex.FunctionalCoefficient.AuxiliaryMatrixAlgebra D) :
    M ∈ auxiliaryMatrixIdeal J ↔
      ∀ i j n, M i j n ∈ J := by
  rw [auxiliaryMatrixIdeal, TwoSidedIdeal.mem_mk']
  simp only [Set.mem_setOf_eq, mem_boundedSequenceIdeal_iff]

/-- A diagonal constant belongs to the matrix ideal exactly as needed for
restriction of the auxiliary GNS representation. -/
theorem diagonalConstants_mem_auxiliaryMatrixIdeal (J : TwoSidedIdeal D)
    {d : D} (hd : d ∈ J) :
    MathlibAnnex.FunctionalCoefficient.diagonalConstants d ∈ auxiliaryMatrixIdeal J := by
  rw [mem_auxiliaryMatrixIdeal_iff]
  intro i j n
  fin_cases i <;> fin_cases j <;>
    simp [MathlibAnnex.FunctionalCoefficient.diagonalConstants,
      MathlibAnnex.MatrixContraction.diagonalHom_00,
      MathlibAnnex.MatrixContraction.diagonalHom_01,
      MathlibAnnex.MatrixContraction.diagonalHom_10,
      MathlibAnnex.MatrixContraction.diagonalHom_11, hd, J.zero_mem]

/-- The coefficient auxiliary state annihilates the whole matrix ideal when
the original functional annihilates `J`. -/
theorem auxiliaryState_eq_zero_of_mem_auxiliaryMatrixIdeal
    (F : StrongDual ℂ D) (J : TwoSidedIdeal D)
    (hF : ∀ d : D, d ∈ J → F d = 0)
    {M : MathlibAnnex.FunctionalCoefficient.AuxiliaryMatrixAlgebra D}
    (hM : M ∈ auxiliaryMatrixIdeal J) :
    MathlibAnnex.FunctionalCoefficient.auxiliaryState F M = 0 := by
  let U := (MathlibAnnex.FunctionalCoefficient.attainingUnitary F :
    MathlibAnnex.FunctionalCoefficient.AuxiliaryMatrixAlgebra D)
  let s : ℕ →ᵇ D := MathlibAnnex.MatrixContraction.entryMap (U * M)
  have hs (n : ℕ) : s n ∈ J := by
    dsimp only [s, U]
    rw [MathlibAnnex.MatrixContraction.entryMap_apply,
      CStarMatrix.mul_apply, Fin.sum_univ_two]
    exact J.add_mem
      (J.mul_mem_left _ _ ((mem_auxiliaryMatrixIdeal_iff J M).1 hM 0 1 n))
      (J.mul_mem_left _ _ ((mem_auxiliaryMatrixIdeal_iff J M).1 hM 1 1 n))
  have hvalues : (fun n : ℕ => F (s n)) = fun _ => (0 : ℂ) := by
    funext n
    exact hF (s n) (hs n)
  have hextend : MathlibAnnex.SequenceFunctional.extend F s = 0 := by
    apply MathlibAnnex.SequenceFunctional.extend_of_tendsto F s 0
    rw [hvalues]
    exact tendsto_const_nhds
  change (‖F‖ : ℂ)⁻¹ * MathlibAnnex.SequenceFunctional.extend F s = 0
  rw [hextend, mul_zero]

end PointwiseIdeals

end MathlibAnnex.Analysis.CStarAlgebra
