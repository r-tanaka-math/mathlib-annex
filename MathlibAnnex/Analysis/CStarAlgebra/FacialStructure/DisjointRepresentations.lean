/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.Representation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Adapters
import MathlibAnnex.Analysis.CStarAlgebra.Intertwiner

/-!
# Intertwiners of inequivalent nonunital representations

Canonical unitization preserves and reflects unitary equivalence. An
intertwiner for the original algebra extends to its unitization on the same
Hilbert spaces. Bounded Schur theory then makes every intertwiner between
inequivalent nonzero irreducible representations zero. Kernels are not used
to decide equivalence, and no direct sum is asserted to be irreducible.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Unitary equivalence is reflected, as well as preserved, by unitization. -/
theorem unitaryEquivalent_unitization_iff
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K) :
    pi.unitization.UnitaryEquivalent sigma.unitization ↔ pi.UnitaryEquivalent sigma := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨U, fun a x => by simpa only [unitization_inr] using hU (Unitization.inr a) x⟩
  · exact unitization_unitaryEquivalent

/-- Intertwining on the original algebra and its canonical unitization agree. -/
theorem intertwines_unitization_iff
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (V : H →L[ℂ] K) :
    _root_.StarAlgHom.Intertwines pi.unitization sigma.unitization V ↔
      ∀ a : A, V.comp (pi a) = (sigma a).comp V := by
  constructor
  · intro h a
    simpa only [unitization_inr] using h (Unitization.inr a)
  · intro h z
    induction z using Unitization.ind with
    | inl_add_inr c a =>
      apply ContinuousLinearMap.ext
      intro x
      have hx := congrArg (fun T : H →L[ℂ] K => T x) (h a)
      change V (pi a x) = sigma a (V x) at hx
      simpa [unitization, ContinuousLinearMap.comp_apply, hx]

/-- Nonzero irreducibility, not equality or inequality of kernels, is the
hypothesis needed to apply the existing bounded-intertwiner theorem. -/
theorem eq_zero_of_intertwines_of_not_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible)
    (hne : ¬ pi.UnitaryEquivalent sigma) (V : H →L[ℂ] K)
    (hV : ∀ a : A, V.comp (pi a) = (sigma a).comp V) : V = 0 := by
  letI : Nontrivial H := pi.nontrivial_of_isNonzero hpi.1
  letI : Nontrivial K := sigma.nontrivial_of_isNonzero hsigma.1
  have hp := Representation.isIrreducible_starAlgHom pi.unitization
    (isIrreducible_unitization pi hpi)
  have hs := Representation.isIrreducible_starAlgHom sigma.unitization
    (isIrreducible_unitization sigma hsigma)
  have hno : ∀ U : H ≃ₗᵢ[ℂ] K,
      ¬ _root_.StarAlgHom.Intertwines pi.unitization sigma.unitization
        (U : H →L[ℂ] K) := by
    intro U hU
    apply hne
    refine ⟨U, ?_⟩
    intro a x
    have h := congrArg (fun T : H →L[ℂ] K => T x) (hU (Unitization.inr a))
    simpa only [ContinuousLinearMap.comp_apply, unitization_inr,
      LinearIsometryEquiv.coe_coe''] using h
  exact _root_.StarAlgHom.Intertwines.eq_zero_of_no_unitary hp hs hno
    ((intertwines_unitization_iff pi sigma V).2 hV)

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
