/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertSumWeakOperatorTopology
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.WeakOperatorDichotomy

/-!
# Joint weak closure in the ambient operator algebra

Transport the actual product-WOT density criterion to the ambient operator
space on the finite dependent Hilbert sum. In particular, for two nonzero
irreducible representations, unitary equivalence and equality with the full
block-diagonal weak closure are exhaustive and mutually exclusive. The
norm-controlled original-algebra interpolation theorems are separate results.
-/

set_option autoImplicit false
noncomputable section
open Set Topology

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] [DecidableEq I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- The diagonal of the original-algebra coordinate values is exactly the
existing atomic representation of the unitization restricted to `A`. -/
theorem diagonalWOT_pi_eq_atomicRepresentation
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i)) (a : A) :
    diagonalWOT (fun i => ContinuousLinearMapWOT.ofCLM (pi i a)) =
      ContinuousLinearMapWOT.ofCLM
        (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a)) := by
  apply ContinuousLinearMapWOT.ext
  intro x
  apply lp.ext
  funext i
  simp only [diagonalWOT_apply, ContinuousLinearMapWOT.ofCLM_apply,
    atomicRepresentation_apply, unitization_inr]

/-- The two topology models give equivalent full-closure assertions, even
without irreducibility or nonzero hypotheses. -/
theorem closure_range_atomic_wot_eq_blockDiagonalWOT_iff_denseRange_pi_wot
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i)) :
    closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
      (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a)))) =
        blockDiagonalWOT (H := H) ↔
      DenseRange (fun a : A => fun i => ContinuousLinearMapWOT.ofCLM (pi i a)) := by
  let W : A → (∀ i, H i →WOT[ℂ] H i) :=
    fun a i => ContinuousLinearMapWOT.ofCLM (pi i a)
  let R : A → (HilbertSum H →WOT[ℂ] HilbertSum H) := fun a =>
    ContinuousLinearMapWOT.ofCLM
      (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a))
  have hR (a : A) : diagonalWOT (W a) = R a :=
    diagonalWOT_pi_eq_atomicRepresentation pi a
  have hC (a : A) : coordinateWOT (R a) = W a := by
    rw [← hR, coordinateWOT_diagonalWOT]
  change closure (Set.range R) = blockDiagonalWOT ↔ DenseRange W
  constructor
  · intro hclosure T
    have hT : diagonalWOT T ∈ closure (Set.range R) := by
      rw [hclosure]
      exact diagonalWOT_mem_blockDiagonalWOT T
    have hmap : Set.MapsTo coordinateWOT (Set.range R) (Set.range W) := by
      rintro _ ⟨a, rfl⟩
      exact ⟨a, (hC a).symm⟩
    have h := hmap.closure continuous_coordinateWOT hT
    simpa only [coordinateWOT_diagonalWOT] using h
  · intro hdense
    apply Set.Subset.antisymm
    · apply closure_minimal _ isClosed_blockDiagonalWOT
      rintro _ ⟨a, rfl⟩
      rw [← hR]
      exact diagonalWOT_mem_blockDiagonalWOT (W a)
    · intro T hT
      rw [← range_diagonalWOT] at hT
      obtain ⟨S, rfl⟩ := hT
      have hmap : Set.MapsTo diagonalWOT (Set.range W) (Set.range R) := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a, (hR a).symm⟩
      exact hmap.closure continuous_diagonalWOT (hdense S)

/-- Full joint weak closure equals the block-diagonal algebra precisely for
pairwise inequivalent nonzero irreducible coordinates. -/
theorem closure_range_atomic_wot_eq_blockDiagonalWOT_iff
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible) :
    closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
      (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a)))) =
        blockDiagonalWOT (H := H) ↔
      ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k) :=
  (closure_range_atomic_wot_eq_blockDiagonalWOT_iff_denseRange_pi_wot pi).trans
    (denseRange_pi_wot_iff_pairwise_not_unitaryEquivalent pi hirr)

section TwoCoordinates
variable {K : Bool → Type w}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The two alternatives of Notes 11.12 in the ambient Hilbert-sum model.
The argument does not infer unitary equivalence from equality of kernels. -/
theorem unitaryEquivalent_or_closure_range_atomic_wot_eq_blockDiagonalWOT
    (pi : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hirr : ∀ i, (pi i).IsIrreducible) :
    (pi false).UnitaryEquivalent (pi true) ∨
      closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
        (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a)))) =
          blockDiagonalWOT (H := K) := by
  by_cases h : (pi false).UnitaryEquivalent (pi true)
  · exact Or.inl h
  · right
    apply (closure_range_atomic_wot_eq_blockDiagonalWOT_iff pi hirr).mpr
    intro i j hij hequiv
    cases i <;> cases j
    · exact hij rfl
    · exact h hequiv
    · apply h
      obtain ⟨U, hU⟩ := hequiv
      refine ⟨U.symm, ?_⟩
      intro a x
      apply U.injective
      simpa only [U.apply_symm_apply] using (hU a (U.symm x)).symm
    · exact hij rfl

/-- The two alternatives are mutually exclusive; this is not implied by
merely proving their disjunction. -/
theorem not_unitaryEquivalent_and_closure_range_atomic_wot_eq_blockDiagonalWOT
    (pi : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hirr : ∀ i, (pi i).IsIrreducible) :
    ¬ ((pi false).UnitaryEquivalent (pi true) ∧
      closure (Set.range (fun a : A => ContinuousLinearMapWOT.ofCLM
        (atomicRepresentation (fun i => (pi i).unitization) (Unitization.inr a)))) =
          blockDiagonalWOT (H := K)) := by
  rintro ⟨hequiv, hclosure⟩
  exact (closure_range_atomic_wot_eq_blockDiagonalWOT_iff pi hirr).mp hclosure
    false true (by decide) hequiv

end TwoCoordinates
end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
