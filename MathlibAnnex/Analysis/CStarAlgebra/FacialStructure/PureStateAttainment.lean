/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment
import MathlibAnnex.Analysis.CStarAlgebra.State.NonUnitalApproximation
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.PureIrreducible

/-!
# Positive norm attainment of a pure state

This is Theorem 11.1 of *A Very Short Course on Operator Algebras*,
October 2025, p. 73, for a genuinely nonunital C-star algebra as well as a
unital one. We use the actual GNS representation of the canonical state
extension to the canonical unitization and restrict its action to the original
algebra. The restriction is proved nonzero and irreducible. The positive
norm-one attaining element is produced in the original algebra.

This construction uses neither a hypothesized cyclic vector for the nonunital
GNS nor a new representation interface. The pre-existing normalized-positive
state predicates and GNS objects are retained. It does not claim the extremal
polar-decomposition or maximal-face results later in the notes.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- A pure norm-one positive functional attains one at a positive norm-one
element of the original C-star algebra. The algebra need not have a unit. -/
theorem exists_nonneg_apply_eq_one_norm_eq_one_of_isPureNonUnitalState
    (phi : A →L[ℂ] ℂ) (hpure : IsPureNonUnitalState A phi) :
    ∃ a : A, 0 ≤ a ∧ phi a = 1 ∧ ‖a‖ = 1 := by
  have hphi : phi ∈ nonUnitalStateSpace A := by
    rw [IsPureNonUnitalState, mem_extremePoints_iff_left] at hpure
    exact hpure.1
  let Phi : Unitization ℂ A →L[ℂ] ℂ := unitizationExtension phi
  have hPhi : Phi ∈ stateSpace (Unitization ℂ A) :=
    unitizationExtension_mem_stateSpace phi hphi
  have hPhiPure : IsPureState (Unitization ℂ A) Phi :=
    isPureState_unitizationExtension phi hphi hpure
  let f : Unitization ℂ A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace Phi hPhi
  let xi : f.GNS := stateGNSVector Phi hPhi
  have hxi : ‖xi‖ = 1 := norm_stateGNSVector Phi hPhi
  have hxi_ne : xi ≠ 0 := by
    intro hz
    simpa [hz] using hxi
  letI : Nontrivial f.GNS := ⟨⟨xi, 0, hxi_ne⟩⟩
  let rho : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
  let pi : NonUnitalCStarRepresentation A f.GNS :=
    rho.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hcoeff (a : A) : inner ℂ xi (pi a xi) = phi a := by
    change inner ℂ (stateGNSVector Phi hPhi)
      ((positiveLinearMapOfMemStateSpace Phi hPhi).gnsStarAlgHom
        (Unitization.inr a) (stateGNSVector Phi hPhi)) = phi a
    rw [inner_gnsStarAlgHom_stateGNSVector]
    exact unitizationExtension_inr phi a
  have hrho : rho.IsIrreducible := by
    apply (Representation.isIrreducible_iff_starAlgHom rho).2
    exact MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom Phi hPhi hPhiPure
  have hnonzero : pi.IsNonzero := by
    change ∃ a : A, pi a ≠ 0
    by_contra! hz
    have hzero : phi = 0 := by
      ext a
      rw [← hcoeff a, hz a]
      simp
    have hnorm := hphi.2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hpi : pi.IsIrreducible :=
    NonUnitalCStarRepresentation.isIrreducible_restriction_of_isIrreducible_unitization
      rho hrho hnonzero
  obtain ⟨a, ha, hanorm, hfix⟩ :=
    NonUnitalCStarRepresentation.exists_nonneg_norm_eq_one_and_apply_eq_self_of_isIrreducible
      pi hpi xi hxi
  refine ⟨a, ha, ?_, hanorm⟩
  rw [← hcoeff a, hfix, inner_self_eq_norm_sq_to_K, hxi]
  norm_num

end NonUnital

/-- The same attainment statement for the existing unital pure-state predicate.
In this specialization the original unit is already an attaining element. -/
theorem exists_nonneg_apply_eq_one_norm_eq_one_of_isPureState
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (phi : B →L[ℂ] ℂ) (hpure : IsPureState B phi) :
    ∃ b : B, 0 ≤ b ∧ phi b = 1 ∧ ‖b‖ = 1 := by
  have hphi : phi ∈ stateSpace B := by
    rw [IsPureState, mem_extremePoints_iff_left] at hpure
    exact hpure.1
  have hne : (1 : B) ≠ 0 := by
    intro hz
    have hone := hphi.2
    rw [hz, map_zero] at hone
    exact zero_ne_one hone
  letI : Nontrivial B := ⟨⟨1, 0, hne⟩⟩
  refine ⟨1, ?_, hphi.2, norm_one⟩
  simpa only [star_one, one_mul] using star_mul_self_nonneg (1 : B)

end MathlibAnnex.Analysis.CStarAlgebra
