/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.AmplifiedCommutant
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicRestriction
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousOrbit

/-!
# Simultaneous finite-vector approximation with repeated summands

Classwise diagonal targets belong to the closed original-algebra orbit in
an arbitrarily amplified Hilbert sum. A finite-test consequence allows any
finite number of vectors in each inequivalent irreducible representation.
No linear independence is required, and the direct sum is not asserted to
be irreducible. The approximating algebra element has no norm control and
is not asserted to be self-adjoint or positive.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

open MathlibAnnex.Analysis.InnerProductSpace

universe u v w t
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} {J : I → Type t} {H : I → Type w}
variable [DecidableEq I] [∀ i, DecidableEq (J i)]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Classwise diagonal action belongs to the closed original-algebra orbit.
Both class and multiplicity index sets may be infinite. The constant `C`
bounds the target operator, not an interpolating algebra element. -/
theorem diagonal_apply_mem_cyclicSubspace_of_pairwise_not_unitaryEquivalent
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : HilbertSum (fun q : Sigma J => H q.1))
    (S : ∀ i, H i →L[ℂ] H i) (C : ℝ) (hC : 0 ≤ C) (hS : ∀ i, ‖S i‖ ≤ C) :
    diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1) x ∈
      cyclicSubspace
        ((atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)).toNonUnitalStarAlgHom.comp
          (Unitization.inrNonUnitalStarAlgHom ℂ A)) x := by
  classical
  let rho := atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
  let sigma : NonUnitalCStarRepresentation A (HilbertSum (fun q : Sigma J => H q.1)) :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let M := cyclicSubspace sigma x
  let P := M.starProjection
  let D := diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1)
  have hU : sigma.unitization = rho := by
    apply Unitization.starAlgHom_ext
    ext a
    simp [sigma, unitization]
  have hred : rho.Reduces M := by
    rw [← hU]
    exact reduces_unitization_of_reduces sigma M (reduces_cyclicSubspace sigma x)
  have hPcomm : _root_.StarAlgHom.InCommutant rho P := by
    intro z
    change P * rho z = rho z * P
    exact Representation.starProjection_commutes_of_reduces rho M hred z
  have hraw (a : A) : rho (Unitization.inr a) (P x) = rho (Unitization.inr a) x :=
    apply_starProjection_cyclicSubspace sigma x a
  have hPx : P x = x := by
    apply lp.ext
    funext q
    have hzero (a : A) : pi q.1 a ((P x) q - x q) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      have ha := congrArg (fun z : HilbertSum (fun q : Sigma J => H q.1) => z q) (hraw a)
      simpa only [rho, atomicRepresentation_apply, unitization_inr] using ha
    apply sub_eq_zero.mp
    by_contra hv
    obtain ⟨a, _, hfix⟩ := exists_norm_eq_one_apply_eq_self_of_ne_zero
      (pi q.1) (hirr q.1) hv
    exact hv (hfix.symm.trans (hzero a))
  have hPD : Commute P D :=
    commute_diagonal_of_amplified_inCommutant pi hirr hne P hPcomm S C hC hS
  have hPDx := congrArg
    (fun T : HilbertSum (fun q : Sigma J => H q.1) →L[ℂ]
      HilbertSum (fun q : Sigma J => H q.1) => T x) hPD.eq
  change P (D x) = D (P x) at hPDx
  rw [hPx] at hPDx
  exact M.starProjection_eq_self_iff.mp hPDx

/-- One original-algebra element approximates a classwise diagonal action
on a Hilbert-summable tuple of repeated vectors. There is no bound on `‖a‖`. -/
theorem exists_atomic_apply_sub_diagonal_norm_lt
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : HilbertSum (fun q : Sigma J => H q.1))
    (S : ∀ i, H i →L[ℂ] H i) (C : ℝ) (hC : 0 ≤ C) (hS : ∀ i, ‖S i‖ ≤ C)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, ‖atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)
      (Unitization.inr a) x - diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1) x‖ <
        epsilon := by
  let sigma : NonUnitalCStarRepresentation A (HilbertSum (fun q : Sigma J => H q.1)) :=
    (atomicRepresentation (fun q : Sigma J => (pi q.1).unitization)).toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let D := diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1)
  have hmem : D x ∈ closure (Set.range (orbitMap sigma x)) :=
    diagonal_apply_mem_cyclicSubspace_of_pairwise_not_unitaryEquivalent
      pi hirr hne x S C hC hS
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hmem epsilon hepsilon
  obtain ⟨a, rfl⟩ := hy
  refine ⟨a, ?_⟩
  simpa only [orbitMap_apply, sigma, D, dist_eq_norm, norm_sub_rev,
    NonUnitalStarAlgHom.comp_apply, StarAlgHom.coe_toNonUnitalStarAlgHom,
    Unitization.inrNonUnitalStarAlgHom_apply] using hdist

/-- Simultaneous strong approximation on arbitrary finite vector tests in
finitely many inequivalent representations. Repeated or zero vectors are
allowed. This does not claim exact interpolation or a norm bound on `a`. -/
theorem exists_forall_apply_sub_norm_lt_of_finite_vector_tests
    [Fintype I] [∀ i, Fintype (J i)]
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (x : ∀ i, J i → H i) (S : ∀ i, H i →L[ℂ] H i)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : A, ∀ i j, ‖pi i a (x i j) - S i (x i j)‖ < epsilon := by
  classical
  let C : ℝ := ∑ i : I, ‖S i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => norm_nonneg (S i))
  have hS (i : I) : ‖S i‖ ≤ C := by
    exact Finset.single_le_sum (fun k _ => norm_nonneg (S k)) (Finset.mem_univ i)
  let xi : HilbertSum (fun q : Sigma J => H q.1) :=
    ⟨fun q => x q.1 q.2, Memℓp.all _⟩
  obtain ⟨a, ha⟩ := exists_atomic_apply_sub_diagonal_norm_lt pi hirr hne xi S C hC hS hepsilon
  refine ⟨a, fun i j => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (atomicRepresentation (fun q : Sigma J => (pi q.1).unitization) (Unitization.inr a) xi -
      diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1) xi) ⟨i, j⟩
  have hbound : ‖pi i a (x i j) - S i (x i j)‖ ≤
      ‖atomicRepresentation (fun q : Sigma J => (pi q.1).unitization) (Unitization.inr a) xi -
        diagonal (fun q : Sigma J => S q.1) C hC (fun q => hS q.1) xi‖ := by
    change ‖(pi i).unitization (Unitization.inr a) (x i j) - S i (x i j)‖ ≤ _ at hcoord
    simpa only [unitization_inr] using hcoord
  exact hbound.trans_lt ha

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
