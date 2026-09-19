import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Ordinary Hilbert-space representations and unitary equivalence.  The target
Hilbert space and its universe remain arbitrary.  Irreducibility explicitly
includes nonzeroness and quantifies over closed reducing subspaces.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u}
variable [Semiring A] [Algebra ℂ A] [Star A]

/-- A unital complex star representation on a Hilbert space. -/
abbrev Representation (A : Type u) [Semiring A] [Algebra ℂ A] [Star A]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  A →⋆ₐ[ℂ] (H →L[ℂ] H)

section Reducing

variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A representation is nonzero if some represented element is nonzero. -/
def Representation.IsNonzero (pi : Representation A H) : Prop :=
  ∃ a : A, pi a ≠ 0

/-- A unital representation on a nontrivial Hilbert space is nonzero. -/
theorem Representation.isNonzero_of_nontrivial [Nontrivial H]
    (pi : Representation A H) : pi.IsNonzero := by
  refine ⟨1, ?_⟩
  simpa using (one_ne_zero : (1 : H →L[ℂ] H) ≠ 0)

/-- A closed subspace invariant under the representation and all adjoints. -/
def Representation.Reduces (pi : Representation A H) (K : Submodule ℂ H) : Prop :=
  IsClosed (K : Set H) ∧
    ∀ (a : A) (x : H), x ∈ K →
      pi a x ∈ K ∧ ContinuousLinearMap.adjoint (pi a) x ∈ K

/-- Irreducibility in the closed-reducing-subspace sense, with nonzero action. -/
def Representation.IsIrreducible (pi : Representation A H) : Prop :=
  pi.IsNonzero ∧ ∀ K : Submodule ℂ H, pi.Reduces K → K = ⊥ ∨ K = ⊤

end Reducing

section Equivalence

variable {H : Type v} {K : Type w} {L : Type z}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Unitary equivalence of representations, including the full intertwining law. -/
def Representation.UnitaryEquivalent (pi : Representation A H)
    (rho : Representation A K) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] K, ∀ (a : A) (x : H), U (pi a x) = rho a (U x)

theorem Representation.unitaryEquivalent_refl (pi : Representation A H) :
    pi.UnitaryEquivalent pi := by
  refine ⟨LinearIsometryEquiv.refl ℂ H, ?_⟩
  simp

theorem Representation.unitaryEquivalent_symm {pi : Representation A H}
    {rho : Representation A K} (h : pi.UnitaryEquivalent rho) :
    rho.UnitaryEquivalent pi := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun a y ↦ ?_⟩
  have h' := congrArg U.symm (hU a (U.symm y))
  simpa using h'.symm

theorem Representation.unitaryEquivalent_trans {pi : Representation A H}
    {rho : Representation A K} {sigma : Representation A L}
    (hpr : pi.UnitaryEquivalent rho) (hrs : rho.UnitaryEquivalent sigma) :
    pi.UnitaryEquivalent sigma := by
  obtain ⟨U, hU⟩ := hpr
  obtain ⟨V, hV⟩ := hrs
  refine ⟨U.trans V, fun a x ↦ ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [hU, hV]

end Equivalence

section UniqueModel

variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
A displayed faithful irreducible representation that captures every nonzero
irreducible representation, with no restriction on the target Hilbert space or
its universe.
-/
def Representation.IsUniqueIrreducibleModel (pi : Representation A H) : Prop :=
  Function.Injective pi ∧ pi.IsIrreducible ∧
    ∀ (K : Type w) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (rho : Representation A K), rho.IsIrreducible → pi.UnitaryEquivalent rho

end UniqueModel

end MathlibAnnex.Analysis.CStarAlgebra
