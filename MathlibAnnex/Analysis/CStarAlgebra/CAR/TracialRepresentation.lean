import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialCyclic
import MathlibAnnex.Analysis.CStarAlgebra.State.ExtensionOfEmbedding
import MathlibAnnex.Analysis.CStarAlgebra.Representation.SimpleFaithful

/-!
# A separable faithful representation of the same shell-family target

The state is extended onto the existing concrete algebra before any new
representation is introduced. Its ordinary GNS representation is then proved
separable, and the already established closed-ideal dichotomy proves it
faithful. No irreducibility of this representation is assumed.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- The CAR trace extends to a state of the actual target. -/
theorem exists_state_extension_trace (family : RepresentativeShellFamily) :
    ∃ φ : ShellFamilyTarget family →L[ℂ] ℂ,
      φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family) ∧
      ∀ b, φ (shellFamilySourceHom family b) = trace b :=
  exists_state_extension_of_injective (shellFamilySourceHom family)
    (shellFamilySourceHom_injective family) trace trace_one norm_trace_le

/-- A state extension of the source trace, chosen on the same concrete algebra. -/
noncomputable def traceExtension (family : RepresentativeShellFamily) :
    ShellFamilyTarget family →L[ℂ] ℂ :=
  Classical.choose (exists_state_extension_trace family)

theorem traceExtension_mem_stateSpace (family : RepresentativeShellFamily) :
    traceExtension family ∈
      MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family) :=
  (Classical.choose_spec (exists_state_extension_trace family)).1

@[simp]
theorem traceExtension_shellFamilySourceHom (family : RepresentativeShellFamily) (b : Limit) :
    traceExtension family (shellFamilySourceHom family b) = trace b :=
  (Classical.choose_spec (exists_state_extension_trace family)).2 b

/-- The positive-linear-map bundle of the chosen extension. -/
noncomputable def traceExtensionPositive (family : RepresentativeShellFamily) :
    ShellFamilyTarget family →ₚ[ℂ] ℂ :=
  positiveLinearMapOfMemStateSpace (traceExtension family)
    (traceExtension_mem_stateSpace family)

@[simp]
theorem traceExtensionPositive_apply (family : RepresentativeShellFamily)
    (a : ShellFamilyTarget family) :
    traceExtensionPositive family a = traceExtension family a := rfl

@[simp]
theorem traceExtensionPositive_one (family : RepresentativeShellFamily) :
    traceExtensionPositive family 1 = 1 := (traceExtension_mem_stateSpace family).2

/-- The ordinary GNS Hilbert space of the state on the actual target. -/
abbrev TracialHilbertSpace (family : RepresentativeShellFamily) :=
  (traceExtensionPositive family).GNS

/-- The canonical unit vector of the target-state GNS construction. -/
noncomputable def tracialVector (family : RepresentativeShellFamily) :
    TracialHilbertSpace family := (traceExtensionPositive family).gnsCyclicVector

/-- The target's GNS representation, not merely a representation of its CAR source. -/
noncomputable def tracialRepresentation (family : RepresentativeShellFamily) :
    Representation (ShellFamilyTarget family) (TracialHilbertSpace family) :=
  (traceExtensionPositive family).gnsStarAlgHom

@[simp]
theorem norm_tracialVector (family : RepresentativeShellFamily) :
    ‖tracialVector family‖ = 1 :=
  (traceExtensionPositive family).norm_gnsCyclicVector (traceExtensionPositive_one family)

theorem tracialVector_ne_zero (family : RepresentativeShellFamily) :
    tracialVector family ≠ 0 := by
  intro hzero
  have h := norm_tracialVector family
  rw [hzero, norm_zero] at h
  exact zero_ne_one h

/-- This nontriviality proof remains separate from the representation proof. -/
theorem nontrivial_tracialHilbertSpace (family : RepresentativeShellFamily) :
    Nontrivial (TracialHilbertSpace family) :=
  nontrivial_of_ne (tracialVector family) 0 (tracialVector_ne_zero family)

@[simp]
theorem inner_tracialVector_tracialRepresentation (family : RepresentativeShellFamily)
    (a : ShellFamilyTarget family) :
    inner ℂ (tracialVector family) (tracialRepresentation family a (tracialVector family)) =
      traceExtension family a :=
  (traceExtensionPositive family).inner_gnsCyclicVector_gnsStarAlgHom a

/-- The source restriction implements the original CAR trace exactly. -/
theorem vectorFunctional_tracialRepresentation_source (family : RepresentativeShellFamily)
    (b : Limit) :
    Representation.vectorFunctional
      ((tracialRepresentation family).comp (shellFamilySourceHom family))
      (tracialVector family) b = trace b := by
  change inner ℂ (tracialVector family)
    (tracialRepresentation family (shellFamilySourceHom family b) (tracialVector family)) = _
  rw [inner_tracialVector_tracialRepresentation, traceExtension_shellFamilySourceHom]

theorem denseRange_tracialRepresentation_orbit (family : RepresentativeShellFamily) :
    DenseRange (fun a ↦ tracialRepresentation family a (tracialVector family)) :=
  (traceExtensionPositive family).denseRange_gnsStarAlgHom_apply_gnsCyclicVector

/-- The CAR orbit, although smaller than the target orbit algebraically,
is already dense in this Hilbert space. -/
theorem denseRange_tracialRepresentation_source_orbit (family : RepresentativeShellFamily) :
    DenseRange (fun b ↦ tracialRepresentation family
      (shellFamilySourceHom family b) (tracialVector family)) :=
  denseRange_source_orbit_of_trace_of_cyclic family (tracialRepresentation family)
    (tracialVector family) (vectorFunctional_tracialRepresentation_source family)
    (denseRange_tracialRepresentation_orbit family)

theorem separableSpace_tracialHilbertSpace (family : RepresentativeShellFamily) :
    TopologicalSpace.SeparableSpace (TracialHilbertSpace family) :=
  separableSpace_of_trace_of_cyclic family (tracialRepresentation family)
    (tracialVector family) (vectorFunctional_tracialRepresentation_source family)
    (denseRange_tracialRepresentation_orbit family)

/-- Faithfulness follows from the previously proved ideal dichotomy of the
same target, after the representation has actually been constructed. -/
theorem tracialRepresentation_injective (family : RepresentativeShellFamily) :
    Function.Injective (tracialRepresentation family) := by
  letI : Nontrivial (TracialHilbertSpace family) := nontrivial_tracialHilbertSpace family
  exact Representation.injective_of_closed_ideal_dichotomy
    (shellFamilyTarget_closedIdeal_dichotomy family) (tracialRepresentation family)

theorem isometry_tracialRepresentation (family : RepresentativeShellFamily) :
    Isometry (tracialRepresentation family) :=
  AddMonoidHomClass.isometry_of_norm (tracialRepresentation family)
    (NonUnitalStarAlgHom.norm_map (tracialRepresentation family)
      (tracialRepresentation_injective family))

end MathlibAnnex.CStarAlgebra.CAR
