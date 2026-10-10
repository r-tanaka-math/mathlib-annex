/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.DisjointRepresentations
import MathlibAnnex.Analysis.CStarAlgebra.Representation.AtomicCommutant

/-!
# Scalar diagonal commutants for finite nonunital families

For a finite dependent family of pairwise inequivalent nonzero irreducible
representations, the commutant of their unitized direct sum consists of
coordinatewise scalar operators. The fibers remain arbitrary Hilbert spaces.
The proof uses the existing atomic blocks and bounded Schur theorem, and
retains a bound on every scalar by the norm of the commuting operator.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} {H : I → Type w}
variable [Fintype I] [DecidableEq I]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- A commuting operator on the finite atomic sum is scalar on each fiber.
The finite-index assumption does not restrict the dimensions of the fibers. -/
theorem exists_forall_apply_eq_smul_of_atomic_inCommutant
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i j, i ≠ j → ¬ (pi i).UnitaryEquivalent (pi j))
    (T : HilbertSum H →L[ℂ] HilbertSum H)
    (hT : _root_.StarAlgHom.InCommutant
      (atomicRepresentation (fun i => (pi i).unitization)) T) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ ‖T‖) ∧
      ∀ (x : HilbertSum H) (i : I), T x i = c i • x i := by
  classical
  letI : ∀ i, Nontrivial (H i) := fun i => (pi i).nontrivial_of_isNonzero (hirr i).1
  have hdiag (i : I) : ∃ c : ℂ,
      atomicBlock T i i = algebraMap ℂ (H i →L[ℂ] H i) c := by
    apply _root_.StarAlgHom.eq_algebraMap_of_irreducible (pi i).unitization
      (Representation.isIrreducible_starAlgHom _ (isIrreducible_unitization _ (hirr i)))
    intro a
    exact intertwines_atomicBlock_of_inCommutant (fun i => (pi i).unitization) T hT i i a
  choose c hc using hdiag
  have hoff {i j : I} (hij : i ≠ j) : atomicBlock T i j = 0 := by
    apply eq_zero_of_intertwines_of_not_unitaryEquivalent
      (pi i) (pi j) (hirr i) (hirr j) (hne i j hij)
    exact (intertwines_unitization_iff _ _ _).1
      (intertwines_atomicBlock_of_inCommutant (fun i => (pi i).unitization) T hT i j)
  have hsingle (i : I) (x : H i) :
      T (coordinateEmbedding i x) = coordinateEmbedding i (c i • x) := by
    apply lp.ext
    funext j
    by_cases hji : j = i
    · subst j
      have h := congrArg (fun R : H i →L[ℂ] H i => R x) (hc i)
      simpa [atomicBlock, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.algebraMap_apply, coordinateEmbedding_apply] using h
    · have h := congrArg (fun R : H i →L[ℂ] H j => R x) (hoff (Ne.symm hji))
      simpa [atomicBlock, ContinuousLinearMap.comp_apply,
        coordinateEmbedding_apply, hji] using h
  have hcnorm (i : I) : ‖c i‖ ≤ ‖T‖ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H i)
    have h := T.le_opNorm (coordinateEmbedding i x)
    rw [hsingle, norm_coordinateEmbedding, norm_smul, norm_coordinateEmbedding] at h
    nlinarith [norm_pos_iff.mpr hx]
  refine ⟨c, hcnorm, ?_⟩
  intro x j
  have hxsum : x = ∑ i : I, coordinateEmbedding i (x i) := by
    have hsum : HasSum (fun i : I => coordinateEmbedding i (x i)) x := by
      simpa [coordinateEmbedding_apply] using
        (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x)
    exact hsum.unique (hasSum_fintype _)
  calc
    T x j = (T (∑ i : I, coordinateEmbedding i (x i))) j := by rw [← hxsum]
    _ = ∑ i : I, (T (coordinateEmbedding i (x i))) j := by
      rw [map_sum]
      exact map_sum (coordinateProjection j)
        (fun i : I => T (coordinateEmbedding i (x i))) Finset.univ
    _ = ∑ i : I, (coordinateEmbedding i (c i • x i)) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hsingle]
    _ = c j • x j := by
      classical
      simp only [coordinateEmbedding_apply, lp.coeFn_single]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij.symm]
      · intro hj
        simp at hj

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
