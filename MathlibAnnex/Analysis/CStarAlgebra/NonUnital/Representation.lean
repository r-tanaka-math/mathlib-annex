import Mathlib.Analysis.CStarAlgebra.Unitization
import MathlibAnnex.Analysis.CStarAlgebra.Representation.Basic

/-!
# Representations of genuinely nonunital C-star algebras

This interface is distinct from `NonUnitalRepresentation`, which has a
unital domain and merely permits a map not known to preserve its unit.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A representation of a possibly genuinely nonunital complex C-star
algebra. -/
abbrev NonUnitalCStarRepresentation (A : Type u)
    [NonUnitalCStarAlgebra A] (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  A →⋆ₙₐ[ℂ] (H →L[ℂ] H)

namespace NonUnitalCStarRepresentation

def IsNonzero (pi : NonUnitalCStarRepresentation A H) : Prop :=
  ∃ a : A, pi a ≠ 0

def Reduces (pi : NonUnitalCStarRepresentation A H)
    (L : Submodule ℂ H) : Prop :=
  IsClosed (L : Set H) ∧
    ∀ (a : A) (x : H), x ∈ L →
      pi a x ∈ L ∧ ContinuousLinearMap.adjoint (pi a) x ∈ L

def IsIrreducible (pi : NonUnitalCStarRepresentation A H) : Prop :=
  pi.IsNonzero ∧ ∀ L : Submodule ℂ H, pi.Reduces L → L = ⊥ ∨ L = ⊤

def UnitaryEquivalent (pi : NonUnitalCStarRepresentation A H)
    (rho : NonUnitalCStarRepresentation A K) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ (a : A) (x : H), U (pi a x) = rho a (U x)

/-- Extend a representation of `A` to the minimal unitization on the same
Hilbert space. -/
noncomputable def unitization (pi : NonUnitalCStarRepresentation A H) :
    Representation (Unitization ℂ A) H :=
  Unitization.starLift pi

@[simp]
theorem unitization_inr
    (pi : NonUnitalCStarRepresentation A H) (a : A) :
    pi.unitization (Unitization.inr a) = pi a := by
  simp [unitization]

@[simp]
theorem unitization_inr_apply
    (pi : NonUnitalCStarRepresentation A H) (a : A) (x : H) :
    pi.unitization (Unitization.inr a) x = pi a x := by
  simp [unitization]

theorem nontrivial_of_isNonzero
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsNonzero) :
    Nontrivial H := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  obtain ⟨a, ha⟩ := hpi
  exact ha (Subsingleton.elim (pi a) 0)

/-- A subspace reducing a nonunital representation also reduces its
canonical unitization extension. -/
theorem reduces_unitization_of_reduces
    (pi : NonUnitalCStarRepresentation A H) (L : Submodule ℂ H)
    (hL : pi.Reduces L) : pi.unitization.Reduces L := by
  refine ⟨hL.1, ?_⟩
  have hinv : ∀ (z : Unitization ℂ A) (x : H), x ∈ L →
      pi.unitization z x ∈ L := by
    intro z
    induction z using Unitization.ind with
    | inl_add_inr c a =>
        intro x hx
        have hax : pi a x ∈ L := (hL.2 a x hx).1
        simpa [unitization] using L.add_mem (L.smul_mem c hx) hax
  intro z x hx
  refine ⟨hinv z x hx, ?_⟩
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  exact hinv (star z) x hx

/-- Restriction of an irreducible representation of the unitization is
irreducible whenever its action on the original algebra is nonzero. -/
theorem isIrreducible_restriction_of_isIrreducible_unitization
    (rho : Representation (Unitization ℂ A) H)
    (hirr : rho.IsIrreducible)
    (hnz : IsNonzero
      (rho.toNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A))) :
    IsIrreducible
      (rho.toNonUnitalStarAlgHom.comp
        (Unitization.inrNonUnitalStarAlgHom ℂ A)) := by
  let sigma : NonUnitalCStarRepresentation A H :=
    rho.toNonUnitalStarAlgHom.comp
      (Unitization.inrNonUnitalStarAlgHom ℂ A)
  refine ⟨hnz, ?_⟩
  intro L hL
  have heq : sigma.unitization = rho := by
    apply Unitization.starAlgHom_ext
    ext a
    simp [sigma, unitization]
  have hred : rho.Reduces L := by
    rw [← heq]
    exact reduces_unitization_of_reduces sigma L hL
  exact hirr.2 L hred

/-- The unitization extension of a nonzero irreducible representation is
irreducible. -/
theorem isIrreducible_unitization
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible) :
    pi.unitization.IsIrreducible := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hirr.1
    refine ⟨Unitization.inr a, ?_⟩
    intro hzero
    apply ha
    ext x
    have := congrArg (fun T : H →L[ℂ] H => T x) hzero
    simpa using this
  · intro L hL
    apply hirr.2 L
    refine ⟨hL.1, ?_⟩
    intro a x hx
    have hz := hL.2 (Unitization.inr a) x hx
    simpa only [unitization_inr] using hz

/-- Unitary equivalence is preserved by canonical unitization. -/
theorem unitization_unitaryEquivalent
    {pi : NonUnitalCStarRepresentation A H}
    {rho : NonUnitalCStarRepresentation A K}
    (h : pi.UnitaryEquivalent rho) :
    pi.unitization.UnitaryEquivalent rho.unitization := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, ?_⟩
  intro z
  induction z using Unitization.ind with
  | inl_add_inr c a =>
      intro x
      simp [unitization, hU]

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
