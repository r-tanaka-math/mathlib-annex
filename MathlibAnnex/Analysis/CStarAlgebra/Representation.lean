import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Unitary equivalence of star representations

This file records the ordinary pointed-free equivalence relation between
representations on possibly different complex Hilbert spaces.  No dimension or
separability hypothesis is imposed.
-/

set_option autoImplicit false

namespace StarAlgHom

variable {A H K L : Type*}
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Two Hilbert-space star representations are unitarily equivalent. -/
def UnitaryEquivalent (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ (a : A) (x : H), U (π a x) = σ a (U x)

theorem unitaryEquivalent_refl (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    UnitaryEquivalent π π := by
  refine ⟨LinearIsometryEquiv.refl ℂ H, ?_⟩
  simp

theorem UnitaryEquivalent.symm
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    (h : UnitaryEquivalent π σ) : UnitaryEquivalent σ π := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, ?_⟩
  intro a x
  apply U.injective
  rw [U.apply_symm_apply, hU]
  simp

theorem UnitaryEquivalent.trans
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    {τ : A →⋆ₐ[ℂ] (L →L[ℂ] L)}
    (h₁ : UnitaryEquivalent π σ) (h₂ : UnitaryEquivalent σ τ) :
    UnitaryEquivalent π τ := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨V, hV⟩ := h₂
  refine ⟨U.trans V, ?_⟩
  intro a x
  simp only [LinearIsometryEquiv.trans_apply]
  rw [hU, hV]

end StarAlgHom
