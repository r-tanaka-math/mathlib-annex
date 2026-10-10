/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.MatrixCoefficient.FiniteRelations
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.WeakOperatorDensity
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientLinear

/-!
# Finite coefficient relations in an irreducible representation

Finite sums of matrix coefficients are WOT-continuous. The received density
theorem, specialized to a singleton family of representations, identifies
relations on the original nonunital algebra with relations on all bounded
operators. No rank-one operator is asserted to lie in the representation
image, and no spectral-cutoff construction is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set Topology
open scoped BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type w} [Fintype ι]

/-- Negation in the source is ordinary linear negation. -/
@[simp]
theorem matrixCoefficient_neg_left (pi : NonUnitalCStarRepresentation A H) (x y : H) :
    matrixCoefficient pi (-x) y = -matrixCoefficient pi x y := by
  ext a
  simp [matrixCoefficient_apply]

/-- A finite relation on the image holds on all bounded operators, by genuine WOT density. -/
theorem sum_matrixCoefficient_eq_zero_iff_sum_operator_matrixCoefficient_eq_zero
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : ι → H) :
    (∑ j, matrixCoefficient pi (x j) (y j)) = 0 ↔
      (∑ j, InnerProductSpace.matrixCoefficient ℂ (x j) (y j)) = 0 := by
  classical
  constructor
  · intro h
    let F : (Unit → H →WOT[ℂ] H) → ℂ :=
      fun T => ∑ j, inner ℂ (y j) (T () (x j))
    have hF : Continuous F := by
      apply continuous_finset_sum
      intro j _
      exact (ContinuousLinearMapWOT.continuous_dual_apply
        (x j) (innerSL ℂ (y j))).comp (continuous_apply ())
    have hclosed : IsClosed {T | F T = 0} := isClosed_eq hF continuous_const
    have hrange : Set.range (fun a : A => fun _ : Unit =>
        ContinuousLinearMapWOT.ofCLM (pi a)) ⊆ {T | F T = 0} := by
      rintro _ ⟨a, rfl⟩
      have ha := congrArg (fun f : StrongDual ℂ A => f a) h
      simpa [F, matrixCoefficient_apply] using ha
    ext T
    have hdense := denseRange_pi_wot_of_pairwise_not_unitaryEquivalent
      (fun _ : Unit => pi) (fun _ => hpi)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (fun _ : Unit => ContinuousLinearMapWOT.ofCLM T)
    have hz := (closure_minimal hrange hclosed) hdense
    simpa [F] using hz
  · intro h
    ext a
    have ha := congrArg
      (fun f : (H →L[ℂ] H) →L[ℂ] ℂ => f (pi a)) h
    simpa [matrixCoefficient_apply] using ha

/-- Lemma 6.7, with the conjugation present in the original PDF.
The finite index can be empty; all vectors can be zero or dependent. -/
theorem sum_matrixCoefficient_eq_zero_iff_exists_matrix
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : ι → H) :
    (∑ j, matrixCoefficient pi (x j) (y j)) = 0 ↔
      ∃ C : Matrix ι ι ℂ,
        (∀ k, ∑ j, star (C j k) • x j = 0) ∧
        (∀ j, ∑ k, C j k • y k = y j) := by
  rw [sum_matrixCoefficient_eq_zero_iff_sum_operator_matrixCoefficient_eq_zero pi hpi]
  exact InnerProductSpace.sum_matrixCoefficient_eq_zero_iff_exists_matrix x y

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
