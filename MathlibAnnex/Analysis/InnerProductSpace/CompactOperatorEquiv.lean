/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.CStarAlgebra.Hom
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric equivalences of compact-operator algebras

Conjugation by a complex-linear Hilbert isometry equivalence preserves compact
operators in both directions and induces the actual nonunital star equivalence.
This module has no direct-sum or geometric-structure-space dependency.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra ENNReal

namespace LinearIsometryEquiv

universe uH uK

variable {H : Type uH} {K : Type uK}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Conjugation by a complex-linear unitary preserves compactness. -/
theorem isCompactOperator_conj_iff (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    IsCompactOperator (U.conjStarAlgEquiv T) ↔ IsCompactOperator T := by
  constructor
  · intro hT
    have heq : T = U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (U.conjStarAlgEquiv T) ∘L U.toContinuousLinearEquiv.toContinuousLinearMap := by
      ext x
      simp
    rw [heq]
    exact (hT.comp_clm U.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  · intro hT
    have heq : U.conjStarAlgEquiv T =
        U.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
      ext y
      rfl
    rw [heq]
    exact (hT.comp_clm U.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      U.toContinuousLinearEquiv.toContinuousLinearMap

/-- The actual star-algebra equivalence of concrete compact-operator
subalgebras induced by a complex-linear unitary. -/
def compactOperatorStarAlgEquiv (U : H ≃ₗᵢ[ℂ] K) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H ≃⋆ₐ[ℂ]
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K where
  toFun T := ⟨U.conjStarAlgEquiv T.1, (isCompactOperator_conj_iff U T.1).2 T.2⟩
  invFun T := ⟨U.symm.conjStarAlgEquiv T.1,
    (isCompactOperator_conj_iff U.symm T.1).2 T.2⟩
  left_inv T := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change U.symm (U (T.1 (U.symm (U x)))) = T.1 x
    simp
  right_inv T := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    change U (U.symm (T.1 (U (U.symm x)))) = T.1 x
    simp
  map_add' S T := Subtype.ext (_root_.map_add U.conjStarAlgEquiv S.1 T.1)
  map_mul' S T := Subtype.ext (map_mul U.conjStarAlgEquiv S.1 T.1)
  map_smul' c T := Subtype.ext (_root_.map_smul U.conjStarAlgEquiv c T.1)
  map_star' T := Subtype.ext (map_star U.conjStarAlgEquiv T.1)

@[simp]
theorem compactOperatorStarAlgEquiv_apply_coe
    (U : H ≃ₗᵢ[ℂ] K)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    ((U.compactOperatorStarAlgEquiv T :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) : K →L[ℂ] K) =
      U.conjStarAlgEquiv T.1 := rfl

@[simp]
theorem compactOperatorStarAlgEquiv_apply_apply
    (U : H ≃ₗᵢ[ℂ] K)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) (y : K) :
    (U.compactOperatorStarAlgEquiv T : K →L[ℂ] K) y =
      U (T.1 (U.symm y)) := rfl

@[simp]
theorem compactOperatorStarAlgEquiv_symm_apply_coe
    (U : H ≃ₗᵢ[ℂ] K)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) :
    (((U.compactOperatorStarAlgEquiv).symm T :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) : H →L[ℂ] H) =
      U.symm.conjStarAlgEquiv T.1 := rfl

@[simp]
theorem compactOperatorStarAlgEquiv_symm_apply_apply
    (U : H ≃ₗᵢ[ℂ] K)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K) (x : H) :
    ((U.compactOperatorStarAlgEquiv).symm T : H →L[ℂ] H) x =
      U.symm (T.1 (U x)) := rfl

@[simp]
theorem norm_compactOperatorStarAlgEquiv_apply
    (U : H ≃ₗᵢ[ℂ] K)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H) :
    ‖U.compactOperatorStarAlgEquiv T‖ = ‖T‖ := by
  have h := (NonUnitalStarAlgHom.isometry U.compactOperatorStarAlgEquiv.toNonUnitalStarAlgHom
    U.compactOperatorStarAlgEquiv.injective).dist_eq T 0
  change dist (U.compactOperatorStarAlgEquiv T) (U.compactOperatorStarAlgEquiv 0) = dist T 0 at h
  simpa only [_root_.map_zero, dist_zero_right] using h

end LinearIsometryEquiv
