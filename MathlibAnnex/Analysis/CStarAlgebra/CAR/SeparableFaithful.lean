import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceGNSModel
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceState
import MathlibAnnex.Analysis.CStarAlgebra.CAR.SeparableIrreducible
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CyclicRestriction

/-!
# The separably represented ordinary Naimark endpoint

The carrier remains exactly `AtomicCounterexampleAlgebra`. Its faithful
separable representation is reducible and has no nonzero irreducible closed
subrepresentation. These are separate conclusions from uniqueness of the
abstract irreducible representation class.
-/

set_option autoImplicit false

open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

universe v

/-- The separable Hilbert space for the single previously selected target. -/
abbrev SeparableCounterexampleHilbertSpace := TraceHilbertSpace

/-- A faithful representation of exactly the existing atomic counterexample
on a separable Hilbert space. -/
noncomputable def separableCounterexampleRepresentation :
    Representation AtomicCounterexampleAlgebra SeparableCounterexampleHilbertSpace :=
  traceModelRepresentation homogeneityShellFamily

theorem separableSpace_separableCounterexampleHilbertSpace :
    TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace :=
  separableSpace_traceHilbertSpace

theorem separableCounterexampleRepresentation_injective :
    Function.Injective separableCounterexampleRepresentation :=
  traceModelRepresentation_injective homogeneityShellFamily

theorem isometry_separableCounterexampleRepresentation :
    Isometry separableCounterexampleRepresentation :=
  isometry_traceModelRepresentation homogeneityShellFamily

theorem not_isIrreducible_separableCounterexampleRepresentation :
    ¬ Representation.IsIrreducible separableCounterexampleRepresentation := by
  letI : TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace :=
    separableSpace_separableCounterexampleHilbertSpace
  exact not_isIrreducible_of_separable
    separableCounterexampleRepresentation.toNonUnitalStarAlgHom

/-- Even passing to an arbitrary closed reducing subspace does not yield a
nonzero irreducible subrepresentation. -/
theorem not_isIrreducible_restrictToReducing_separableCounterexampleRepresentation
    (M : Submodule ℂ SeparableCounterexampleHilbertSpace)
    (hM : separableCounterexampleRepresentation.Reduces M) :
    letI : CompleteSpace M := hM.1.completeSpace_coe
    ¬ Representation.IsIrreducible
      (Representation.restrictToReducing separableCounterexampleRepresentation M hM) := by
  letI : CompleteSpace M := hM.1.completeSpace_coe
  letI : TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace :=
    separableSpace_separableCounterexampleHilbertSpace
  letI : TopologicalSpace.SeparableSpace M := inferInstance
  exact not_isIrreducible_of_separable
    (Representation.restrictToReducing
      separableCounterexampleRepresentation M hM).toNonUnitalStarAlgHom

/-- A closed, fully specified existence statement for the same target;
separability is concluded, not passed as an additional premise. -/
theorem exists_separable_faithful_representation :
    TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace ∧
    ∃ ρ : Representation AtomicCounterexampleAlgebra SeparableCounterexampleHilbertSpace,
      Function.Injective ρ ∧ ¬ ρ.IsIrreducible :=
  ⟨separableSpace_separableCounterexampleHilbertSpace,
    separableCounterexampleRepresentation,
    separableCounterexampleRepresentation_injective,
    not_isIrreducible_separableCounterexampleRepresentation⟩

/-- The stronger conclusion preserves the entire previously proved
ordinary endpoint, including its independent comparison universe. -/
theorem atomicCounterexampleEndpoint_and_separable_faithful_representation :
    AtomicCounterexampleEndpoint.{v} ∧
    TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace ∧
    Function.Injective separableCounterexampleRepresentation ∧
    ¬ Representation.IsIrreducible separableCounterexampleRepresentation :=
  ⟨shellFamilyEndpoint homogeneityShellFamily, separableSpace_separableCounterexampleHilbertSpace,
    separableCounterexampleRepresentation_injective,
    not_isIrreducible_separableCounterexampleRepresentation⟩

/-- The unique trace of the unchanged atomic counterexample. -/
noncomputable def atomicCounterexampleTrace : AtomicCounterexampleAlgebra →L[ℂ] ℂ :=
  traceExtension homogeneityShellFamily

theorem atomicCounterexampleTrace_mem_stateSpace :
    atomicCounterexampleTrace ∈
      MathlibAnnex.Analysis.CStarAlgebra.stateSpace AtomicCounterexampleAlgebra :=
  traceExtension_mem_stateSpace homogeneityShellFamily

theorem atomicCounterexampleTrace_mul_comm (a b : AtomicCounterexampleAlgebra) :
    atomicCounterexampleTrace (a * b) = atomicCounterexampleTrace (b * a) :=
  traceExtension_mul_comm homogeneityShellFamily a b

theorem atomicCounterexampleTrace_star_mul_self_eq_zero_iff
    (a : AtomicCounterexampleAlgebra) :
    atomicCounterexampleTrace (star a * a) = 0 ↔ a = 0 :=
  traceExtension_star_mul_self_eq_zero_iff homogeneityShellFamily a

/-- The trace is implemented by the original CAR trace vector in the
separable faithful model. -/
@[simp]
theorem inner_traceVector_separableCounterexampleRepresentation
    (a : AtomicCounterexampleAlgebra) :
    inner ℂ traceVector (separableCounterexampleRepresentation a traceVector) =
      atomicCounterexampleTrace a :=
  inner_traceVector_traceModelRepresentation homogeneityShellFamily a

theorem eq_atomicCounterexampleTrace_of_mem_stateSpace_of_mul_comm
    (φ : AtomicCounterexampleAlgebra →L[ℂ] ℂ)
    (hφ : φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace AtomicCounterexampleAlgebra)
    (hφtrace : ∀ a b, φ (a * b) = φ (b * a)) : φ = atomicCounterexampleTrace :=
  eq_traceExtension_of_mem_stateSpace_of_mul_comm homogeneityShellFamily φ hφ hφtrace

/-- The final strengthened endpoint uses only previously separated proof
constants. It retains the ordinary endpoint at any comparison universe and
adds the fixed separable faithful model and the faithful unique trace. -/
theorem atomicCounterexampleEndpoint_and_separable_tracial_representation :
    AtomicCounterexampleEndpoint.{v} ∧
    Nontrivial SeparableCounterexampleHilbertSpace ∧
    TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace ∧
    Function.Injective separableCounterexampleRepresentation ∧
    Isometry separableCounterexampleRepresentation ∧
    ¬ Representation.IsIrreducible separableCounterexampleRepresentation ∧
    atomicCounterexampleTrace ∈
      MathlibAnnex.Analysis.CStarAlgebra.stateSpace AtomicCounterexampleAlgebra ∧
    (∀ a b, atomicCounterexampleTrace (a * b) = atomicCounterexampleTrace (b * a)) ∧
    (∀ a, atomicCounterexampleTrace (star a * a) = 0 ↔ a = 0) ∧
    (∀ φ : AtomicCounterexampleAlgebra →L[ℂ] ℂ,
      φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace AtomicCounterexampleAlgebra →
      (∀ a b, φ (a * b) = φ (b * a)) → φ = atomicCounterexampleTrace) :=
  ⟨shellFamilyEndpoint homogeneityShellFamily,
    nontrivial_traceHilbertSpace,
    separableSpace_separableCounterexampleHilbertSpace,
    separableCounterexampleRepresentation_injective,
    isometry_separableCounterexampleRepresentation,
    not_isIrreducible_separableCounterexampleRepresentation,
    atomicCounterexampleTrace_mem_stateSpace,
    atomicCounterexampleTrace_mul_comm,
    atomicCounterexampleTrace_star_mul_self_eq_zero_iff,
    eq_atomicCounterexampleTrace_of_mem_stateSpace_of_mul_comm⟩

/-- The same fixed algebra has a faithful representation on a nontrivial separable
Hilbert space, but has no nonzero irreducible representation on any separable
Hilbert space in the arbitrary comparison universe. This does not assert that
the algebra is nonprimitive: the original irreducible model is retained. -/
theorem atomicCounterexampleEndpoint_and_exists_separable_faithful_representation_and_no_separable_irreducible_representation :
    AtomicCounterexampleEndpoint.{v} ∧
    Nontrivial SeparableCounterexampleHilbertSpace ∧
    TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace ∧
    (∃ ρ : Representation AtomicCounterexampleAlgebra SeparableCounterexampleHilbertSpace,
      Function.Injective ρ) ∧
    (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∀ ρ : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H),
        ¬ ρ.IsIrreducible) := by
  refine ⟨shellFamilyEndpoint homogeneityShellFamily, nontrivial_traceHilbertSpace,
    separableSpace_separableCounterexampleHilbertSpace,
    ⟨separableCounterexampleRepresentation,
      separableCounterexampleRepresentation_injective⟩, ?_⟩
  intro H _ _ _ _ ρ
  exact not_isIrreducible_of_separable ρ

end MathlibAnnex.CStarAlgebra.CAR
