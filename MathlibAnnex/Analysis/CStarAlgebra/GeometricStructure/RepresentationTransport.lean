/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.MatrixCoefficient
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometric transport of nonunital representations

Irreducibility is transported through an actual surjective linear isometry,
using inverse images of closed reducing subspaces. No kernel classification
is assumed. In particular this permits universe enlargement without changing
the represented coefficients.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An actual unitary intertwiner transports nonzero irreducibility. -/
theorem isIrreducible_of_intertwines
    (pi : NonUnitalCStarRepresentation A H)
    (rho : NonUnitalCStarRepresentation A K) (U : H ≃ₗᵢ[ℂ] K)
    (hU : ∀ a x, U (pi a x) = rho a (U x)) (hpi : pi.IsIrreducible) :
    rho.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hpi.1
    refine ⟨a, fun hz => ha ?_⟩
    ext x
    apply U.injective
    simpa only [hz, ContinuousLinearMap.zero_apply, map_zero] using hU a x
  · intro L hL
    let M : Submodule ℂ H := L.comap U.toLinearMap
    have hM : pi.Reduces M := by
      refine ⟨hL.1.preimage U.continuous, ?_⟩
      intro a x hx
      have hinv (b : A) : pi b x ∈ M := by
        change U (pi b x) ∈ L
        rw [hU]
        exact (hL.2 b (U x) hx).1
      refine ⟨hinv a, ?_⟩
      rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      exact hinv (star a)
    rcases hpi.2 M hM with hbot | htop
    · left
      apply le_antisymm ?_ bot_le
      intro y hy
      have hx : U.symm y ∈ M := by
        change U (U.symm y) ∈ L
        simpa using hy
      rw [hbot, Submodule.mem_bot] at hx
      have : y = 0 := by simpa using congrArg U hx
      exact (Submodule.mem_bot (R := ℂ) (x := y)).mpr this
    · right
      apply top_unique
      intro y _
      have hx : U.symm y ∈ M := by rw [htop]; trivial
      change U (U.symm y) ∈ L at hx
      simpa using hx

/-- Conjugation of a representation by a surjective linear isometry. -/
def conj (pi : NonUnitalCStarRepresentation A H) (U : H ≃ₗᵢ[ℂ] K) :
    NonUnitalCStarRepresentation A K :=
  U.conjStarAlgEquiv.toStarAlgHom.toNonUnitalStarAlgHom.comp pi

@[simp]
theorem conj_apply (pi : NonUnitalCStarRepresentation A H)
    (U : H ≃ₗᵢ[ℂ] K) (a : A) (y : K) :
    conj pi U a y = U (pi a (U.symm y)) := rfl

/-- Conjugation preserves nonzero irreducibility. -/
theorem isIrreducible_conj (pi : NonUnitalCStarRepresentation A H)
    (U : H ≃ₗᵢ[ℂ] K) (hpi : pi.IsIrreducible) :
    (conj pi U).IsIrreducible := by
  refine isIrreducible_of_intertwines pi (conj pi U) U ?_ hpi
  intro a x
  simp only [conj_apply, U.symm_apply_apply]

/-- Isometric conjugation preserves the coefficient, including its phase. -/
@[simp]
theorem matrixCoefficient_conj (pi : NonUnitalCStarRepresentation A H)
    (U : H ≃ₗᵢ[ℂ] K) (x y : H) :
    matrixCoefficient (conj pi U) (U x) (U y) = matrixCoefficient pi x y := by
  ext a
  simp only [matrixCoefficient_apply, conj_apply, U.symm_apply_apply, U.inner_map_map]

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
