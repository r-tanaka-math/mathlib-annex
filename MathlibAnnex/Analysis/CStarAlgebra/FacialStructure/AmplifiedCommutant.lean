/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.DisjointRepresentations
import MathlibAnnex.Analysis.CStarAlgebra.Representation.AtomicCommutant
import Mathlib.Tactic

/-!
# Commutants with repeated irreducible summands

The index `i` labels pairwise inequivalent representations and `J i` labels
copies of the same representation. Blocks within one class are scalar
matrices, not necessarily diagonal matrices. Blocks between different
classes vanish. Classwise diagonal operators commute with this commutant.
Both index types may be arbitrary, and the Hilbert spaces need not be
finite-dimensional or separable. This is a commutant theorem, not an
algebra-norm-controlled interpolation theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} {J : I → Type t} {H : I → Type w}
variable [DecidableEq I] [∀ i, DecidableEq (J i)]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Any two copies of the same irreducible representation contribute a
scalar block. Every scalar entry is bounded by the norm of the whole operator. -/
theorem exists_atomicBlock_eq_algebraMap_of_same_class
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (T : HilbertSum (fun k : Sigma J => H k.1) →L[ℂ]
      HilbertSum (fun k : Sigma J => H k.1))
    (hT : _root_.StarAlgHom.InCommutant
      (atomicRepresentation (fun k : Sigma J => (pi k.1).unitization)) T)
    (i : I) (j k : J i) :
    ∃ c : ℂ, atomicBlock T ⟨i, j⟩ ⟨i, k⟩ = algebraMap ℂ (H i →L[ℂ] H i) c ∧
      ‖c‖ ≤ ‖T‖ := by
  letI : ∀ i, Nontrivial (H i) := fun i => (pi i).nontrivial_of_isNonzero (hirr i).1
  obtain ⟨c, hc⟩ : ∃ c : ℂ,
      atomicBlock T ⟨i, j⟩ ⟨i, k⟩ = algebraMap ℂ (H i →L[ℂ] H i) c := by
    apply _root_.StarAlgHom.eq_algebraMap_of_irreducible (pi i).unitization
      (Representation.isIrreducible_starAlgHom _ (isIrreducible_unitization _ (hirr i)))
    intro a
    exact intertwines_atomicBlock_of_inCommutant
      (fun q : Sigma J => (pi q.1).unitization) T hT ⟨i, j⟩ ⟨i, k⟩ a
  refine ⟨c, hc, ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  have heval : atomicBlock T ⟨i, j⟩ ⟨i, k⟩ x = c • x := by
    rw [hc, ContinuousLinearMap.algebraMap_apply]
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (T (coordinateEmbedding (⟨i, j⟩ : Sigma J) x)) ⟨i, k⟩
  have hbound : ‖c‖ * ‖x‖ ≤ ‖T‖ * ‖x‖ := by
    calc
      ‖c‖ * ‖x‖ = ‖atomicBlock T ⟨i, j⟩ ⟨i, k⟩ x‖ := by rw [heval, norm_smul]
      _ ≤ ‖T (coordinateEmbedding (⟨i, j⟩ : Sigma J) x)‖ := hcoord
      _ ≤ ‖T‖ * ‖x‖ := by
        simpa only [norm_coordinateEmbedding] using
          T.le_opNorm (coordinateEmbedding (⟨i, j⟩ : Sigma J) x)
  nlinarith [norm_pos_iff.mpr hx]

/-- Distinct equivalence classes have zero blocks, including between arbitrary
copies. Equality of representation kernels is not used as a substitute for equivalence. -/
theorem atomicBlock_eq_zero_of_different_classes
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (T : HilbertSum (fun q : Sigma J => H q.1) →L[ℂ]
      HilbertSum (fun q : Sigma J => H q.1))
    (hT : _root_.StarAlgHom.InCommutant
      (atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)) T)
    {i k : I} (hik : i ≠ k) (j : J i) (l : J k) :
    atomicBlock T ⟨i, j⟩ ⟨k, l⟩ = 0 := by
  letI : ∀ i, Nontrivial (H i) := fun i => (pi i).nontrivial_of_isNonzero (hirr i).1
  apply eq_zero_of_intertwines_of_not_unitaryEquivalent
    (pi i) (pi k) (hirr i) (hirr k) (hne i k hik)
  exact (intertwines_unitization_iff _ _ _).1
    (intertwines_atomicBlock_of_inCommutant
      (fun q : Sigma J => (pi q.1).unitization) T hT ⟨i, j⟩ ⟨k, l⟩)

/-- An arbitrary uniformly bounded classwise operator commutes with the
commutant of the amplified representation. Same-class scalar off-diagonal
blocks are retained. The arbitrary-index passage uses the convergent
finite-support expansion in the genuine Hilbert sum. -/
theorem commute_diagonal_of_amplified_inCommutant
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (T : HilbertSum (fun q : Sigma J => H q.1) →L[ℂ]
      HilbertSum (fun q : Sigma J => H q.1))
    (hT : _root_.StarAlgHom.InCommutant
      (atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)) T)
    (S : ∀ i, H i →L[ℂ] H i) (C : ℝ) (hC : 0 ≤ C) (hS : ∀ i, ‖S i‖ ≤ C) :
    Commute T (diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1)) := by
  classical
  let D := diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1)
  have hDsingle (q : Sigma J) (x : H q.1) :
      D (coordinateEmbedding q x) = coordinateEmbedding q (S q.1 x) := by
    apply lp.ext
    funext r
    by_cases hr : r = q
    · subst r
      simp [D, coordinateEmbedding_apply, lp.coeFn_single]
    · simp [D, coordinateEmbedding_apply, lp.coeFn_single, Pi.single_apply, hr]
  have hsingle (q : Sigma J) (x : H q.1) :
      T (D (coordinateEmbedding q x)) = D (T (coordinateEmbedding q x)) := by
    rcases q with ⟨i, j⟩
    rw [hDsingle]
    apply lp.ext
    funext r
    rcases r with ⟨k, l⟩
    change atomicBlock T ⟨i, j⟩ ⟨k, l⟩ (S i x) =
      S k (atomicBlock T ⟨i, j⟩ ⟨k, l⟩ x)
    by_cases hik : i = k
    · subst k
      obtain ⟨c, hc, _⟩ := exists_atomicBlock_eq_algebraMap_of_same_class pi hirr T hT i j l
      rw [hc]
      simp only [ContinuousLinearMap.algebraMap_apply, map_smul]
    · rw [atomicBlock_eq_zero_of_different_classes pi hirr hne T hT hik j l]
      simp
  rw [commute_iff_eq]
  apply ContinuousLinearMap.ext
  intro x
  have hsum : HasSum (fun q : Sigma J => coordinateEmbedding q (x q)) x := by
    simpa [coordinateEmbedding_apply] using
      (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x)
  have hleft : HasSum (fun q : Sigma J => (T.comp D) (coordinateEmbedding q (x q)))
      ((T.comp D) x) := hsum.mapL (T.comp D)
  have hright : HasSum (fun q : Sigma J => (D.comp T) (coordinateEmbedding q (x q)))
      ((D.comp T) x) := hsum.mapL (D.comp T)
  have hterms : (fun q : Sigma J => (T.comp D) (coordinateEmbedding q (x q))) =
      (fun q : Sigma J => (D.comp T) (coordinateEmbedding q (x q))) := by
    funext q
    exact hsingle q (x q)
  rw [hterms] at hleft
  exact hleft.unique hright

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
