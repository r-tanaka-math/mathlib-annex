import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TracialTransport

/-!
# Uniqueness of the extension of the CAR trace

This is uniqueness among all state extensions, not merely among traces.
-/

set_option autoImplicit false

open scoped InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- Any state extending the original CAR trace is the chosen extension. -/
theorem eq_traceExtension_of_mem_stateSpace_of_apply_shellFamilySourceHom_eq_trace
    (family : RepresentativeShellFamily) (φ : ShellFamilyTarget family →L[ℂ] ℂ)
    (hφ : φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family))
    (hφB : ∀ b, φ (shellFamilySourceHom family b) = trace b) :
    φ = traceExtension family := by
  let f := positiveLinearMapOfMemStateSpace φ hφ
  let ρ : Representation (ShellFamilyTarget family) f.GNS := f.gnsStarAlgHom
  let ξ : f.GNS := f.gnsCyclicVector
  have hξ (b : Limit) : Representation.vectorFunctional
      (ρ.comp (shellFamilySourceHom family)) ξ b = trace b := by
    change inner ℂ f.gnsCyclicVector (f.gnsStarAlgHom _ f.gnsCyclicVector) = _
    rw [PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom]
    exact hφB b
  have hcyclic : DenseRange (fun a ↦ ρ a ξ) :=
    f.denseRange_gnsStarAlgHom_apply_gnsCyclicVector
  obtain ⟨e, heξ, he⟩ := exists_pointed_unitary_of_trace_of_cyclic family
    ρ (tracialRepresentation family) ξ (tracialVector family) hξ
    (vectorFunctional_tracialRepresentation_source family) hcyclic
    (denseRange_tracialRepresentation_orbit family)
  apply ContinuousLinearMap.ext
  intro a
  calc
    φ a = inner ℂ ξ (ρ a ξ) := (f.inner_gnsCyclicVector_gnsStarAlgHom a).symm
    _ = inner ℂ (e ξ) (e (ρ a ξ)) := (e.inner_map_map ξ (ρ a ξ)).symm
    _ = inner ℂ (tracialVector family)
        (tracialRepresentation family a (tracialVector family)) := by
      have hcoe (y : f.GNS) :
          (e : f.GNS →L[ℂ] TracialHilbertSpace family) y = e y := rfl
      have h := congrArg (fun T : f.GNS →L[ℂ] TracialHilbertSpace family ↦ T ξ) (he a)
      simpa only [ContinuousLinearMap.comp_apply, hcoe, heξ] using
        congrArg (fun y ↦ inner ℂ (e ξ) y) h
    _ = traceExtension family a := inner_tracialVector_tracialRepresentation family a

/-- Existence and uniqueness are on the actual fixed target. -/
theorem existsUnique_state_extension_trace (family : RepresentativeShellFamily) :
    ∃! φ : ShellFamilyTarget family →L[ℂ] ℂ,
      φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family) ∧
        ∀ b, φ (shellFamilySourceHom family b) = trace b := by
  refine ⟨traceExtension family,
    ⟨traceExtension_mem_stateSpace family, traceExtension_shellFamilySourceHom family⟩, ?_⟩
  intro φ hφ
  exact eq_traceExtension_of_mem_stateSpace_of_apply_shellFamilySourceHom_eq_trace family φ hφ.1 hφ.2

end MathlibAnnex.CStarAlgebra.CAR
