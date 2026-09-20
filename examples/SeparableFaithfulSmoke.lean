import MathlibAnnex.Analysis.CStarAlgebra.CAR.SeparableFaithful

/-! Build-stage tests only; not a public Project entry. -/
set_option autoImplicit false
set_option pp.universes true

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.CAR

universe v

example : AtomicCounterexampleAlgebra = ShellFamilyTarget homogeneityShellFamily := rfl

example : SeparableCounterexampleHilbertSpace = tracePositive.GNS := rfl

example : separableCounterexampleRepresentation =
    traceModelRepresentation homogeneityShellFamily := rfl

example : AtomicCounterexampleEndpoint.{v} :=
  (atomicCounterexampleEndpoint_and_separable_tracial_representation.{v}).1

#check @atomicCounterexampleEndpoint_and_separable_tracial_representation
#check @not_isIrreducible_restrictToReducing_separableCounterexampleRepresentation
#check @existsUnique_state_extension_trace
#check @existsUnique_tracial_state
#check @traceExtension_star_mul_self_eq_zero_iff
#check @traceModelRepresentation_shellFamilySourceHom
#check @stronglyConverges_traceRepresentation_shell_sums
#check @traceModelRepresentation_shellFamilyGenerator_mem_unitary

/- Typed probes: separability is a conclusion; the exclusion is universal,
not merely nonirreducibility of the selected faithful representation. -/
example : TopologicalSpace.SeparableSpace SeparableCounterexampleHilbertSpace ∧
    ∃ ρ : Representation AtomicCounterexampleAlgebra SeparableCounterexampleHilbertSpace,
      Function.Injective ρ := by
  have h := atomicCounterexampleEndpoint_and_exists_separable_faithful_representation_and_no_separable_irreducible_representation.{v}
  exact ⟨h.2.2.1, h.2.2.2.1⟩
example (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (ρ : NonUnitalRepresentation (A := AtomicCounterexampleAlgebra) (H := H)) :
    ¬ ρ.IsIrreducible := by
  exact (atomicCounterexampleEndpoint_and_exists_separable_faithful_representation_and_no_separable_irreducible_representation.{v}).2.2.2.2 H ρ
