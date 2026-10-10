/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CoordinateIdeal
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel
import Mathlib.Topology.MetricSpace.Basic

/-!
# Active coordinates of irreducible representations of dependent c₀-sums

A nonzero representation detects a coordinate by finite-truncation norm
approximation.  Primeness of an irreducible kernel kills the complementary
ideal, proving exact factorization and a unique active irreducible restriction.
The fibres are arbitrary nonunital complex C-star algebras, not only compacts.
-/



set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι uA uK

namespace C0DirectSum

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, NonUnitalCStarAlgebra (A i)]

section Representation

variable {K : Type uK}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A nonzero representation detects at least one coordinate ideal.  The proof
uses finite-truncation norm density and contractivity, not a dual decomposition. -/
theorem exists_isNonzero_comp_single
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsNonzero) :
    ∃ i : ι, NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i)) := by
  classical
  obtain ⟨x, hx⟩ := hrho
  have hpos : 0 < ‖rho x‖ := norm_pos_iff.mpr hx
  by_contra hnone
  push_neg at hnone
  have hzero : ∀ (i : ι) (a : A i), rho (single A i a) = 0 := by
    intro i a
    by_contra ha
    exact hnone i ⟨a, ha⟩
  obtain ⟨s, hs⟩ := exists_finset_norm_sub_truncate_lt A x hpos
  have htrunc : rho (truncate A s x) = 0 := by
    rw [truncate_eq_sum_single]
    simp only [map_sum, hzero, Finset.sum_const_zero]
  have hbound := NonUnitalStarAlgHom.norm_apply_le rho (x - truncate A s x)
  rw [map_sub, htrunc, sub_zero] at hbound
  exact (lt_of_le_of_lt hbound hs).false

/-- If one coordinate restriction is nonzero, the complementary coordinate-zero
ideal is contained in the irreducible kernel. -/
theorem complementIdeal_le_kernelIdeal_of_isNonzero_comp_single
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsIrreducible) (i : ι)
    (hi : NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i))) :
    complementIdeal A i ≤ NonUnitalCStarRepresentation.kernelIdeal rho := by
  have hinf : coordinateIdeal A i ⊓ complementIdeal A i ≤
      NonUnitalCStarRepresentation.kernelIdeal rho := by
    rw [coordinateIdeal_inf_complementIdeal]
    exact bot_le
  have hor := (NonUnitalCStarRepresentation.inf_le_kernelIdeal_iff rho hrho
    (coordinateIdeal A i) (complementIdeal A i)).1 hinf
  rcases hor with hcoord | hcomp
  · exfalso
    obtain ⟨a, ha⟩ := hi
    have hmem : single A i a ∈ coordinateIdeal A i := single_mem_coordinateIdeal A i a
    have hker := hcoord hmem
    exact ha ((NonUnitalCStarRepresentation.mem_kernelIdeal rho _).1 hker)
  · exact hcomp

/-- An irreducible representation with active coordinate `i` depends only on
that coordinate. -/
theorem apply_eq_apply_single_eval_of_isNonzero_comp_single
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsIrreducible) (i : ι)
    (hi : NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i))) (x : C0DirectSum A) :
    rho x = rho (single A i (eval A i x)) := by
  have hcomp := complementIdeal_le_kernelIdeal_of_isNonzero_comp_single A rho hrho i hi
  have herase : rho (erase A i x) = 0 :=
    (NonUnitalCStarRepresentation.mem_kernelIdeal rho _).1
      (hcomp (erase_mem_complementIdeal A i x))
  have hdecomp := single_add_erase A i x
  calc
    rho x = rho (single A i (eval A i x) + erase A i x) := by rw [hdecomp]
    _ = rho (single A i (eval A i x)) := by rw [map_add, herase, add_zero]

/-- The active coordinate restriction of an irreducible representation is itself
irreducible. -/
theorem isIrreducible_comp_single_of_isNonzero
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsIrreducible) (i : ι)
    (hi : NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i))) :
    NonUnitalCStarRepresentation.IsIrreducible (rho.comp (single A i)) := by
  refine ⟨hi, ?_⟩
  intro L hL
  apply hrho.2 L
  refine ⟨hL.1, ?_⟩
  intro x z hz
  have heq : rho x = (rho.comp (single A i)) (eval A i x) := by
    change rho x = rho (single A i (eval A i x))
    exact apply_eq_apply_single_eval_of_isNonzero_comp_single A rho hrho i hi x
  rw [heq]
  exact hL.2 (eval A i x) z hz

/-- An irreducible representation has at most one active coordinate. -/
theorem eq_of_isNonzero_comp_single_of_isNonzero_comp_single
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsIrreducible) {i j : ι}
    (hi : NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i)))
    (hj : NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A j))) : i = j := by
  by_contra hij
  have hcomp := complementIdeal_le_kernelIdeal_of_isNonzero_comp_single A rho hrho i hi
  obtain ⟨a, ha⟩ := hj
  have hmem : single A j a ∈ complementIdeal A i := by
    rw [mem_complementIdeal]
    exact eval_single_of_ne A hij a
  have hzero : rho (single A j a) = 0 :=
    (NonUnitalCStarRepresentation.mem_kernelIdeal rho _).1 (hcomp hmem)
  exact ha hzero

/-- Every nonzero irreducible representation has a unique active coordinate. -/
theorem existsUnique_isNonzero_comp_single
    (rho : NonUnitalCStarRepresentation (C0DirectSum A) K)
    (hrho : rho.IsIrreducible) :
    ∃! i : ι, NonUnitalCStarRepresentation.IsNonzero (rho.comp (single A i)) := by
  obtain ⟨i, hi⟩ := exists_isNonzero_comp_single A rho hrho.1
  exact ⟨i, hi, fun j hj => eq_of_isNonzero_comp_single_of_isNonzero_comp_single
    A rho hrho hj hi⟩

end Representation

end C0DirectSum

end MathlibAnnex.Analysis.CStarAlgebra
