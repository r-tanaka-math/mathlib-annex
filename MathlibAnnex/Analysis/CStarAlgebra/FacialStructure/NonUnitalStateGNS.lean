/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PureStateExtreme
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CoefficientTranslate

/-!
# The actual GNS model of a nonunital state

This small interface exposes the existing GNS of the canonical positive
extension to the formal unitization, restricted to the original algebra.
The space, vector and representation are existing constructions, not fields
in a representation-realization axiom. The restriction is nonzero for every
state; purity then gives irreducibility by the pinned GNS theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStateGNS

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- The existing Hilbert GNS space of the canonical positive unitization extension. -/
abbrev Space (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :=
  (positiveLinearMapOfMemStateSpace (unitizationExtension phi)
    (unitizationExtension_mem_stateSpace phi hphi)).GNS

/-- The existing norm-one GNS vector, with no chosen approximate unit. -/
def vector (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) : Space phi hphi :=
  stateGNSVector (unitizationExtension phi) (unitizationExtension_mem_stateSpace phi hphi)

/-- The actual GNS representation restricted to the original algebra. -/
def representation (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    NonUnitalCStarRepresentation A (Space phi hphi) :=
  (positiveLinearMapOfMemStateSpace (unitizationExtension phi)
    (unitizationExtension_mem_stateSpace phi hphi)).gnsStarAlgHom.toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)

@[simp]
theorem norm_vector (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    ‖vector phi hphi‖ = 1 :=
  norm_stateGNSVector (unitizationExtension phi) (unitizationExtension_mem_stateSpace phi hphi)

/-- Recover the original state, rather than only its extension. -/
theorem matrixCoefficient_representation (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    NonUnitalCStarRepresentation.matrixCoefficient (representation phi hphi)
      (vector phi hphi) (vector phi hphi) = phi := by
  ext a
  change inner ℂ (stateGNSVector (unitizationExtension phi) _)
    ((positiveLinearMapOfMemStateSpace (unitizationExtension phi) _).gnsStarAlgHom
      (Unitization.inr a) (stateGNSVector (unitizationExtension phi) _)) = phi a
  rw [inner_gnsStarAlgHom_stateGNSVector]
  exact unitizationExtension_inr phi a

/-- The restricted action is nonzero for every state, before using purity. -/
theorem isNonzero_representation (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A) :
    (representation phi hphi).IsNonzero := by
  change ∃ a : A, representation phi hphi a ≠ 0
  by_contra! hz
  have hzero : phi = 0 := by
    rw [← matrixCoefficient_representation phi hphi]
    ext a
    simp only [NonUnitalCStarRepresentation.matrixCoefficient_apply, hz a,
      ContinuousLinearMap.zero_apply, inner_zero_right]
  have hn := hphi.2
  rw [hzero, norm_zero] at hn
  norm_num at hn

/-- A pure state's concrete GNS restriction is nonzero irreducible. -/
theorem isIrreducible_representation (phi : StrongDual ℂ A)
    (hphi : phi ∈ nonUnitalStateSpace A) (hpure : IsPureNonUnitalState A phi) :
    (representation phi hphi).IsIrreducible := by
  let Phi := unitizationExtension phi
  have hPhi : Phi ∈ stateSpace (Unitization ℂ A) := unitizationExtension_mem_stateSpace phi hphi
  let f := positiveLinearMapOfMemStateSpace Phi hPhi
  let rho : Representation (Unitization ℂ A) f.GNS := f.gnsStarAlgHom
  let v : f.GNS := stateGNSVector Phi hPhi
  have hv : ‖v‖ = 1 := norm_stateGNSVector Phi hPhi
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  letI : Nontrivial f.GNS := ⟨⟨v, 0, hv0⟩⟩
  have hrho : rho.IsIrreducible := by
    apply (Representation.isIrreducible_iff_starAlgHom rho).2
    exact MathlibAnnex.CStarAlgebra.isIrreducible_pureState_gnsStarAlgHom
      Phi hPhi (isPureState_unitizationExtension phi hphi hpure)
  exact NonUnitalCStarRepresentation.isIrreducible_restriction_of_isIrreducible_unitization
    rho hrho (isNonzero_representation phi hphi)

/-- For a pure state the original-algebra orbit of the GNS vector is all of
the Hilbert space. This is not merely cyclicity for the unitization. -/
theorem representation_vector_surjective_of_isPure
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureNonUnitalState A phi) :
    Function.Surjective (fun a : A => representation phi hphi a (vector phi hphi)) := by
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp only [map_zero, ContinuousLinearMap.zero_apply, hy]⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hnC : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  let eta := (‖y‖ : ℂ)⁻¹ • y
  have heta : ‖eta‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  obtain ⟨a, -, ha⟩ :=
    NonUnitalCStarRepresentation.exists_norm_eq_one_and_apply_eq_of_isIrreducible
      (representation phi hphi) (isIrreducible_representation phi hphi hpure)
      (vector phi hphi) eta (norm_vector phi hphi) heta
  refine ⟨(‖y‖ : ℂ) • a, ?_⟩
  change representation phi hphi ((‖y‖ : ℂ) • a) (vector phi hphi) = y
  rw [map_smul]
  change (‖y‖ : ℂ) • (representation phi hphi a (vector phi hphi)) = y
  rw [ha]
  simp only [eta, smul_smul, mul_inv_cancel₀ hnC, one_smul]

/-- The state vector is cyclic for the original, possibly nonunital algebra. -/
theorem denseRange_representation_vector_of_isPure
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureNonUnitalState A phi) :
    DenseRange (fun a : A => representation phi hphi a (vector phi hphi)) :=
  (representation_vector_surjective_of_isPure phi hphi hpure).denseRange

/-- A pure-state translate is a unit coefficient of THIS actual GNS model.
The target carries the adjoint of the translating unitary, as required by
`inner y (pi a x)`. Its unit norm follows from exact coefficient norms and the
already proved isometry of translation. -/
theorem exists_unit_vectors_matrixCoefficient_eq_unitaryTranslate
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureNonUnitalState A phi) (u : unitary (Unitization ℂ A)) :
    ∃ x y : Space phi hphi, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      NonUnitalCStarRepresentation.matrixCoefficient (representation phi hphi) x y =
        unitaryTranslate u phi := by
  let pi := representation phi hphi
  let x := vector phi hphi
  let y := pi.unitization (star (u : Unitization ℂ A)) x
  have hx : ‖x‖ = 1 := norm_vector phi hphi
  have hpi : pi.IsIrreducible := isIrreducible_representation phi hphi hpure
  have hcoef : NonUnitalCStarRepresentation.matrixCoefficient pi x y = unitaryTranslate u phi := by
    calc
      NonUnitalCStarRepresentation.matrixCoefficient pi x y =
          unitaryTranslate u (NonUnitalCStarRepresentation.matrixCoefficient pi x x) :=
        (NonUnitalCStarRepresentation.unitaryTranslate_matrixCoefficient pi x x u).symm
      _ = unitaryTranslate u phi :=
        congrArg (unitaryTranslate u) (matrixCoefficient_representation phi hphi)
  have hy : ‖y‖ = 1 := by
    calc
      ‖y‖ = ‖NonUnitalCStarRepresentation.matrixCoefficient pi x y‖ := by
        rw [NonUnitalCStarRepresentation.norm_matrixCoefficient_of_isIrreducible pi hpi, hx, one_mul]
      _ = ‖unitaryTranslate u phi‖ := congrArg norm hcoef
      _ = 1 := (norm_unitaryTranslate u phi).trans hphi.2
  exact ⟨x, y, hx, hy, hcoef⟩

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalStateGNS
