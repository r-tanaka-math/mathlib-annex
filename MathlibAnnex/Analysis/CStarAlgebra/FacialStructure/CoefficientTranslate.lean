/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.UnitaryTranslate
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.PureStateAttainment
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure

/-!
# Pure-state translation of irreducible matrix coefficients

A unit-vector coefficient in an actual nonzero irreducible representation
admits a unitary translate which is a pure state. The unitary is obtained
from the existing transitivity theorem in the canonical unitization; the
functional and its norm stay on the original algebra.

The source of the coefficient must really be irreducible. The general
`FunctionalCoefficient.recover` representation does not supply this premise.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]

/-- Purity of the canonical extension reflects to a norm-one nonunital state.
The affine identity for the extension is proved with both convex weights. -/
theorem isPureNonUnitalState_of_isPureState_unitizationExtension
    (phi : StrongDual ℂ A) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpure : IsPureState (Unitization ℂ A) (unitizationExtension phi)) :
    IsPureNonUnitalState A phi := by
  rw [IsPureNonUnitalState, mem_extremePoints_iff_left]
  rw [IsPureState, mem_extremePoints_iff_left] at hpure
  refine ⟨hphi, ?_⟩
  intro psi hpsi chi hchi hsegment
  obtain ⟨s, t, hs, ht, hst, hcomb⟩ := hsegment
  have hcombU : s • unitizationExtension psi + t • unitizationExtension chi =
      unitizationExtension phi := by
    apply ContinuousLinearMap.ext
    intro z
    have h := congrArg (fun f : StrongDual ℂ A => f z.snd) hcomb
    change s • psi z.snd + t • chi z.snd = phi z.snd at h
    change s • (z.fst + psi z.snd) + t • (z.fst + chi z.snd) = z.fst + phi z.snd
    calc
      _ = (s + t) • z.fst + (s • psi z.snd + t • chi z.snd) := by module
      _ = _ := by rw [hst, one_smul, h]
  have heq := hpure.2 (unitizationExtension psi) (unitizationExtension_mem_stateSpace psi hpsi)
    (unitizationExtension chi) (unitizationExtension_mem_stateSpace chi hchi)
    ⟨s, t, hs, ht, hst, hcombU⟩
  apply ContinuousLinearMap.ext
  intro a
  simpa only [unitizationExtension_inr] using
    congrArg (fun f : StrongDual ℂ (Unitization ℂ A) => f (Unitization.inr a)) heq

namespace NonUnitalCStarRepresentation

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Diagonal coefficients are positive even without irreducibility. -/
theorem matrixCoefficient_self_nonneg
    (pi : NonUnitalCStarRepresentation A H) (x : H) {a : A} (ha : 0 ≤ a) :
    0 ≤ matrixCoefficient pi x x a := by
  have hpa : 0 ≤ pi a := by simpa only [map_zero] using OrderHomClass.mono pi ha
  simpa only [sub_zero, matrixCoefficient_apply] using hpa.inner_nonneg_right x

/-- Unit vector states of genuine nonunital irreducible representations are pure.
This uses the existing unital converse GNS theorem and reflects purity back. -/
theorem isPureNonUnitalState_matrixCoefficient_self_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x : H) (hx : ‖x‖ = 1) : IsPureNonUnitalState A (matrixCoefficient pi x x) := by
  have hstate : matrixCoefficient pi x x ∈ nonUnitalStateSpace A := by
    refine ⟨fun a ha => matrixCoefficient_self_nonneg pi x ha, ?_⟩
    rw [norm_matrixCoefficient_of_isIrreducible pi hpi x x, hx, one_mul]
  have hpure := MathlibAnnex.CStarAlgebra.isPureState_vectorFunctional_of_isIrreducible
    pi.unitization (isIrreducible_unitization pi hpi) x hx
  have hrest : unitizationRestriction (Representation.vectorFunctional pi.unitization x) =
      matrixCoefficient pi x x := by
    ext a
    simp only [unitizationRestriction_apply, Representation.vectorFunctional_apply,
      matrixCoefficient_apply, unitization_inr]
  have heq := eq_unitizationExtension_of_restriction_eq (matrixCoefficient pi x x)
    (Representation.vectorFunctional pi.unitization x) hpure.1 hrest
  apply isPureNonUnitalState_of_isPureState_unitizationExtension _ hstate
  rwa [heq] at hpure

omit [PartialOrder A] [StarOrderedRing A] in
/-- Left unitary translation acts on the output vector by the adjoint.
The formula uses the convention `inner y (pi a x)`. -/
theorem unitaryTranslate_matrixCoefficient
    (pi : NonUnitalCStarRepresentation A H) (x y : H)
    (u : unitary (Unitization ℂ A)) :
    unitaryTranslate u (matrixCoefficient pi x y) =
      matrixCoefficient pi x (pi.unitization (star (u : Unitization ℂ A)) y) := by
  ext a
  have hmul : pi (unitizationLeftMul (u : Unitization ℂ A) a) =
      pi.unitization (u : Unitization ℂ A) * pi a := by
    calc
      _ = pi.unitization (unitizationLeftMul (u : Unitization ℂ A) a : Unitization ℂ A) :=
        (unitization_inr pi _).symm
      _ = _ := by rw [inr_unitizationLeftMul, map_mul, unitization_inr]
  rw [unitaryTranslate_apply, matrixCoefficient_apply, matrixCoefficient_apply, hmul,
    map_star, ContinuousLinearMap.star_eq_adjoint]
  change inner ℂ y (pi.unitization (u : Unitization ℂ A) (pi a x)) =
    inner ℂ ((pi.unitization (u : Unitization ℂ A)).adjoint y) (pi a x)
  exact (ContinuousLinearMap.adjoint_inner_left
    (pi.unitization (u : Unitization ℂ A)) (pi a x) y).symm

/-- The polar-type decomposition for coefficients already realized in an
irreducible representation. Existence of such a representation for every
extreme dual functional remains a separate theorem. -/
theorem exists_unitaryTranslate_eq_pureState_of_isIrreducible
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ u : unitary (Unitization ℂ A),
      unitaryTranslate u (matrixCoefficient pi x y) = matrixCoefficient pi x x ∧
      IsPureNonUnitalState A (matrixCoefficient pi x x) ∧
      matrixCoefficient pi x y = unitaryTranslate (star u) (matrixCoefficient pi x x) := by
  obtain ⟨u, hu⟩ := Representation.exists_unitary_apply_eq_of_isIrreducible
    pi.unitization (isIrreducible_unitization pi hpi) x y hx hy
  have hstar : pi.unitization (star (u : Unitization ℂ A)) y = x := by
    have hprod : pi.unitization (star (u : Unitization ℂ A)) *
        pi.unitization (u : Unitization ℂ A) = 1 := by
      rw [← map_mul, Unitary.coe_star_mul_self, map_one]
    have h := congrArg (fun T : H →L[ℂ] H => T x) hprod
    change pi.unitization (star (u : Unitization ℂ A))
      (pi.unitization (u : Unitization ℂ A) x) = x at h
    rwa [hu] at h
  have htranslate : unitaryTranslate u (matrixCoefficient pi x y) = matrixCoefficient pi x x := by
    rw [unitaryTranslate_matrixCoefficient, hstar]
  refine ⟨u, htranslate, isPureNonUnitalState_matrixCoefficient_self_of_isIrreducible pi hpi x hx, ?_⟩
  simpa only [unitaryTranslate_star_translate] using
    congrArg (unitaryTranslate (star u)) htranslate

end NonUnitalCStarRepresentation
end MathlibAnnex.Analysis.CStarAlgebra
