/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FunctionalExtension
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.CyclicCoefficient
import MathlibAnnex.Analysis.CStarAlgebra.Representation.FunctionalCoefficient

/-!
# Actual cyclic coefficient realization of nonunital bounded functionals

Hahn--Banach supplies a norm-preserving extension to the unitization. The
fixed `FunctionalCoefficient` construction supplies an actual GNS space,
a representation and two contractive vectors. Restrict to the closed orbit
of the original algebra and project both vectors. The resulting source
vector is cyclic for the original algebra, not merely for its unitization.
Both vectors have norm one for every nonzero functional; recovery retains
the original functional norm as its scalar factor. Extremality of the
extension is neither assumed nor asserted. All objects are explicitly built
from existing constructions; no realization structure is postulated.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalFunctional

open NonUnitalCStarRepresentation

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual auxiliary GNS Hilbert space of the Hahn--Banach extension. -/
abbrev HilbertSpace (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :=
  MathlibAnnex.FunctionalCoefficient.GNSHilbertSpace
    (unitizationDualExtension rho) (unitizationDualExtension_ne_zero hrho)

/-- Restrict the actual coefficient representation to the original algebra. -/
def representation (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    NonUnitalCStarRepresentation A (HilbertSpace rho hrho) :=
  (MathlibAnnex.FunctionalCoefficient.representation
    (unitizationDualExtension rho) (unitizationDualExtension_ne_zero hrho)).toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)

/-- The upstream right vector is the source vector in `inner y (pi a x)`. -/
def sourceVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) : HilbertSpace rho hrho :=
  MathlibAnnex.FunctionalCoefficient.rightVector
    (unitizationDualExtension rho) (unitizationDualExtension_ne_zero hrho)

/-- The upstream left vector is the conjugate-linear target vector. -/
def targetVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) : HilbertSpace rho hrho :=
  MathlibAnnex.FunctionalCoefficient.leftVector
    (unitizationDualExtension rho) (unitizationDualExtension_ne_zero hrho)

theorem norm_sourceVector_le (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖sourceVector rho hrho‖ ≤ 1 :=
  MathlibAnnex.FunctionalCoefficient.norm_rightVector_le _ _

theorem norm_targetVector_le (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖targetVector rho hrho‖ ≤ 1 :=
  MathlibAnnex.FunctionalCoefficient.norm_leftVector_le _ _

/-- Exact recovery on the original algebra, with the original functional norm. -/
theorem recover (rho : StrongDual ℂ A) (hrho : rho ≠ 0) (a : A) :
    rho a = (‖rho‖ : ℂ) * inner ℂ (targetVector rho hrho)
      (representation rho hrho a (sourceVector rho hrho)) := by
  simpa only [representation, sourceVector, targetVector, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom, Unitization.inrNonUnitalStarAlgHom_apply,
    unitizationDualExtension_inr, norm_unitizationDualExtension] using
    MathlibAnnex.FunctionalCoefficient.recover (unitizationDualExtension rho)
      (unitizationDualExtension_ne_zero hrho) (Unitization.inr a)

/-- The actual closed original-algebra cyclic subspace, regarded as a Hilbert space. -/
abbrev CyclicSpace (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :=
  ↥(cyclicSubspace (representation rho hrho) (sourceVector rho hrho))

def cyclicRepresentation (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    NonUnitalCStarRepresentation A (CyclicSpace rho hrho) :=
  cyclicRestriction (representation rho hrho) (sourceVector rho hrho)

def cyclicSourceVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) : CyclicSpace rho hrho :=
  (cyclicSubspace (representation rho hrho) (sourceVector rho hrho)).orthogonalProjectionOnto
    (sourceVector rho hrho)

def cyclicTargetVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) : CyclicSpace rho hrho :=
  (cyclicSubspace (representation rho hrho) (sourceVector rho hrho)).orthogonalProjectionOnto
    (targetVector rho hrho)

/-- Exact recovery after the reducing restriction, without extremality. -/
theorem recover_cyclicRepresentation (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    rho = (‖rho‖ : ℂ) • matrixCoefficient (cyclicRepresentation rho hrho)
      (cyclicSourceVector rho hrho) (cyclicTargetVector rho hrho) := by
  change rho = (‖rho‖ : ℂ) • matrixCoefficient
    (cyclicRestriction (representation rho hrho) (sourceVector rho hrho))
    ((cyclicSubspace (representation rho hrho) (sourceVector rho hrho)).orthogonalProjectionOnto
      (sourceVector rho hrho))
    ((cyclicSubspace (representation rho hrho) (sourceVector rho hrho)).orthogonalProjectionOnto
      (targetVector rho hrho))
  rw [matrixCoefficient_cyclicRestriction]
  ext a
  exact recover rho hrho a

/-- For a norm-one functional, recovery has no scalar factor. -/
theorem matrixCoefficient_cyclicRepresentation_of_norm_eq_one
    (rho : StrongDual ℂ A) (hrho : rho ≠ 0) (hnorm : ‖rho‖ = 1) :
    matrixCoefficient (cyclicRepresentation rho hrho)
      (cyclicSourceVector rho hrho) (cyclicTargetVector rho hrho) = rho := by
  simpa only [hnorm, Complex.ofReal_one, one_smul] using
    (recover_cyclicRepresentation rho hrho).symm

/-- Normalization in the actual upstream model is exact for every nonzero
functional, not only for an extreme functional or a norm-one functional. -/
theorem norm_matrixCoefficient_representation (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖matrixCoefficient (representation rho hrho)
      (sourceVector rho hrho) (targetVector rho hrho)‖ = 1 := by
  have hraw : rho = (‖rho‖ : ℂ) • matrixCoefficient (representation rho hrho)
      (sourceVector rho hrho) (targetVector rho hrho) := by
    ext a
    exact recover rho hrho a
  have hn := congrArg norm hraw
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg rho)] at hn
  apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hrho)
  simpa only [mul_one] using hn.symm

private theorem norm_cyclic_vectors (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖cyclicSourceVector rho hrho‖ = 1 ∧ ‖cyclicTargetVector rho hrho‖ = 1 :=
  norm_orthogonalProjectionOnto_cyclicSubspace_eq_one
    (representation rho hrho) (sourceVector rho hrho) (targetVector rho hrho)
    (norm_sourceVector_le rho hrho) (norm_targetVector_le rho hrho)
    (norm_matrixCoefficient_representation rho hrho)

/-- The constructed original-algebra cyclic source is a unit vector. -/
@[simp]
theorem norm_cyclicSourceVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖cyclicSourceVector rho hrho‖ = 1 := (norm_cyclic_vectors rho hrho).1

/-- The other vector in the constructed original cyclic space is also a unit vector. -/
@[simp]
theorem norm_cyclicTargetVector (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    ‖cyclicTargetVector rho hrho‖ = 1 := (norm_cyclic_vectors rho hrho).2

/-- Both original auxiliary vectors lie in the original-algebra orbit
closure. No extremality or original-algebra nondegeneracy premise is needed. -/
theorem vectors_mem_cyclicSubspace (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    sourceVector rho hrho ∈ cyclicSubspace (representation rho hrho) (sourceVector rho hrho) ∧
    targetVector rho hrho ∈ cyclicSubspace (representation rho hrho) (sourceVector rho hrho) :=
  mem_cyclicSubspace_of_norm_matrixCoefficient_eq_one
    (representation rho hrho) (sourceVector rho hrho) (targetVector rho hrho)
    (norm_sourceVector_le rho hrho) (norm_targetVector_le rho hrho)
    (norm_matrixCoefficient_representation rho hrho)

/-- Cyclicity is explicitly for the action of the original algebra A. -/
theorem denseRange_cyclicRepresentation (rho : StrongDual ℂ A) (hrho : rho ≠ 0) :
    DenseRange (fun a : A => cyclicRepresentation rho hrho a (cyclicSourceVector rho hrho)) :=
  denseRange_cyclicRestriction (representation rho hrho) (sourceVector rho hrho)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalFunctional
