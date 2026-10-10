/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationTransport

/-! # Actual unitary equivalence under composition and Hilbert-space transport -/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w t v' w'
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} {K : Type w} {L : Type t}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Reflexivity is witnessed by the identity isometry. -/
theorem unitaryEquivalent_refl (pi : NonUnitalCStarRepresentation A H) : pi.UnitaryEquivalent pi :=
  ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩

/-- Reverse the actual intertwining isometry. -/
theorem UnitaryEquivalent.symm {pi : NonUnitalCStarRepresentation A H}
    {sigma : NonUnitalCStarRepresentation A K} (h : pi.UnitaryEquivalent sigma) :
    sigma.UnitaryEquivalent pi := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun a y => ?_⟩
  apply U.injective
  simp only [U.apply_symm_apply, hU]

/-- Compose actual intertwining isometries, without any kernel argument. -/
theorem UnitaryEquivalent.trans {pi : NonUnitalCStarRepresentation A H}
    {sigma : NonUnitalCStarRepresentation A K} {tau : NonUnitalCStarRepresentation A L}
    (h : pi.UnitaryEquivalent sigma) (k : sigma.UnitaryEquivalent tau) :
    pi.UnitaryEquivalent tau := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, hV⟩ := k
  exact ⟨U.trans V, fun a x => by simp only [LinearIsometryEquiv.trans_apply, hU, hV]⟩

/-- Conjugation is explicitly unitarily equivalent to the starting representation. -/
theorem unitaryEquivalent_conj (pi : NonUnitalCStarRepresentation A H) (U : H ≃ₗᵢ[ℂ] K) :
    pi.UnitaryEquivalent (conj pi U) := by
  exact ⟨U, fun a x => by simp only [conj_apply, U.symm_apply_apply]⟩

variable {H' : Type v'} {K' : Type w'}
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- Isometric changes of both Hilbert spaces preserve and reflect equivalence. -/
theorem unitaryEquivalent_conj_iff
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (U : H ≃ₗᵢ[ℂ] H') (V : K ≃ₗᵢ[ℂ] K') :
    (conj pi U).UnitaryEquivalent (conj sigma V) ↔ pi.UnitaryEquivalent sigma := by
  constructor
  · intro h
    exact (unitaryEquivalent_conj pi U).trans (h.trans (unitaryEquivalent_conj sigma V).symm)
  · intro h
    exact (unitaryEquivalent_conj pi U).symm.trans (h.trans (unitaryEquivalent_conj sigma V))

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
