/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.CompactAnnihilatingState
import MathlibAnnex.Analysis.CStarAlgebra.State.Ideal
import Mathlib.Topology.Order.Compact
import MathlibAnnex.Analysis.CStarAlgebra.State.MaximizingFace

/-!
# Nonzero singular pure states and actual irreducible separating actions

A real evaluation is maximized on the existing compact annihilator face. An
extreme point of the maximizing face is extreme in the full unital state space.
The positive detecting value is retained. Consequently the restriction of its
GNS representation to the original algebra is nonzero, not the infinity action.

The result is relative to any actual representation having a specified
noncompact image. No quotient C-star structure, simplicity, separability,
faithfulness, or irreducibility of that representation is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The singular pure state detects the specified square in the original
algebra. Its quantitative bound rules out the character at infinity. -/
theorem exists_pureState_annihilating_compacts_of_not_isCompactOperator
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : ¬ IsCompactOperator (pi a)) :
    ∃ phi : StrongDual ℂ (Unitization ℂ A),
      phi ∈ stateSpace (Unitization ℂ A) ∧ IsPureState (Unitization ℂ A) phi ∧
      (∀ j : Unitization ℂ A,
        IsCompactOperator (pi.unitization j) → phi j = 0) ∧
      (Metric.infDist (pi a)
        (compactOperator (RingHom.id ℂ) H H : Set (H →L[ℂ] H))) ^ 2 / 4 ≤
          (phi (star (Unitization.inr a) * Unitization.inr a)).re ∧
      0 < (phi (star (Unitization.inr a) * Unitization.inr a)).re := by
  obtain ⟨psi, hpsi, hbound, hpos⟩ :=
    exists_weakState_annihilating_compacts_of_not_isCompactOperator pi a ha
  let J := MathlibAnnex.CStarAlgebra.compactPreimageIdeal
    pi.unitization.toNonUnitalStarAlgHom
  obtain ⟨phi, hphi, hpure, hann, hdom, hpositive⟩ :=
    exists_pureState_annihilating_of_pos_weakStateFace J
      (star (Unitization.inr a) * Unitization.inr a) psi hpsi hpos
  refine ⟨phi, hphi, hpure, ?_, hbound.trans hdom, hpositive⟩
  intro j hj
  exact hann j ((MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
    pi.unitization.toNonUnitalStarAlgHom j).2 hj)

/-- A pure unitization state with positive value on a square has a nonzero
irreducible restriction. Ideal annihilation holds as an operator equation in
its actual GNS representation, not just as a scalar expectation. -/
theorem isIrreducible_restriction_gns_of_pureState_annihilating
    (pi : NonUnitalCStarRepresentation A H) (a : A)
    (phi : StrongDual ℂ (Unitization ℂ A)) (hphi : phi ∈ stateSpace (Unitization ℂ A))
    (hpure : IsPureState (Unitization ℂ A) phi)
    (hann : ∀ j : Unitization ℂ A, IsCompactOperator (pi.unitization j) → phi j = 0)
    (hpos : 0 < (phi (star (Unitization.inr a) * Unitization.inr a)).re) :
    let f := positiveLinearMapOfMemStateSpace phi hphi
    let rho := f.gnsStarAlgHom.toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)
    NonUnitalCStarRepresentation.IsIrreducible rho ∧ rho a ≠ 0 ∧
      ∀ c : A, IsCompactOperator (pi c) → rho c = 0 := by
  let f := positiveLinearMapOfMemStateSpace phi hphi
  let rhoU : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
  let rho : NonUnitalCStarRepresentation A f.GNS :=
    rhoU.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hxi : ‖stateGNSVector phi hphi‖ = 1 := norm_stateGNSVector phi hphi
  have hxi0 : stateGNSVector phi hphi ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hxi
    exact zero_ne_one hxi
  letI : Nontrivial f.GNS := nontrivial_of_ne (stateGNSVector phi hphi) 0 hxi0
  have hrhoU : rhoU.IsIrreducible := by
    apply (Representation.isIrreducible_iff_starAlgHom rhoU).2
    exact isIrreducible_pureState_gnsStarAlgHom phi hphi hpure
  have hrhoa : rho a ≠ 0 := by
    intro hzero
    have hinr : rhoU (Unitization.inr a) = 0 := hzero
    have hb : rhoU (star (Unitization.inr a) * Unitization.inr a) = 0 := by
      rw [map_mul, map_star, hinr, mul_zero]
    have hv : phi (star (Unitization.inr a) * Unitization.inr a) = 0 := by
      rw [← inner_gnsStarAlgHom_stateGNSVector phi hphi]
      change inner ℂ (stateGNSVector phi hphi)
        (rhoU (star (Unitization.inr a) * Unitization.inr a)
          (stateGNSVector phi hphi)) = 0
      rw [hb, ContinuousLinearMap.zero_apply, inner_zero_right]
    rw [hv, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨NonUnitalCStarRepresentation.isIrreducible_restriction_of_isIrreducible_unitization
    rhoU hrhoU ⟨a, hrhoa⟩, hrhoa, ?_⟩
  intro c hc
  let J := MathlibAnnex.CStarAlgebra.compactPreimageIdeal
    pi.unitization.toNonUnitalStarAlgHom
  have hannJ : ∀ j : Unitization ℂ A, j ∈ J → phi j = 0 := by
    intro j hj
    exact hann j ((MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
      pi.unitization.toNonUnitalStarAlgHom j).1 hj)
  have hcinr : Unitization.inr c ∈ J := by
    apply (MathlibAnnex.CStarAlgebra.mem_compactPreimageIdeal
      pi.unitization.toNonUnitalStarAlgHom (Unitization.inr c)).2
    simpa only [StarAlgHom.coe_toNonUnitalStarAlgHom,
      NonUnitalCStarRepresentation.unitization_inr] using hc
  exact gnsStarAlgHom_eq_zero_of_mem phi hphi J hannJ hcinr

/-- A specified noncompact image yields a genuine nonzero irreducible action
on a Hilbert space in the SOURCE algebra universe. It kills all compact
preimages and still detects the specified element. No quotient action is assumed. -/
theorem exists_isIrreducible_annihilating_compacts_of_not_isCompactOperator
    (pi : NonUnitalCStarRepresentation A H) (a : A) (ha : ¬ IsCompactOperator (pi a)) :
    ∃ (L : Type u) (instN : NormedAddCommGroup L),
      letI := instN
      ∃ instI : InnerProductSpace ℂ L,
        letI := instI
        ∃ instC : CompleteSpace L,
          letI := instC
          ∃ rho : NonUnitalCStarRepresentation A L,
            NonUnitalCStarRepresentation.IsIrreducible rho ∧ rho a ≠ 0 ∧
              ∀ c : A, IsCompactOperator (pi c) → rho c = 0 := by
  obtain ⟨phi, hphi, hpure, hann, _hbound, hpos⟩ :=
    exists_pureState_annihilating_compacts_of_not_isCompactOperator pi a ha
  let f := positiveLinearMapOfMemStateSpace phi hphi
  exact ⟨f.GNS, inferInstance, inferInstance, inferInstance,
    f.gnsStarAlgHom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A),
    isIrreducible_restriction_gns_of_pureState_annihilating pi a phi hphi hpure hann hpos⟩

end MathlibAnnex.Analysis.CStarAlgebra
