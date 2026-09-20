import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceExtensionTracial
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceUnique
import MathlibAnnex.Analysis.CStarAlgebra.GNS.TracialFaithfulness

/-!
# The faithful unique tracial state of the fixed shell-family target

Faithfulness uses the trace identity and the faithful cyclic representation.
Uniqueness among all tracial states follows by restriction to the completed
CAR algebra and the stronger uniqueness theorem for state extensions.
-/

set_option autoImplicit false

open scoped ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- The extended trace detects every nonzero square. This is faithfulness
of the state, not merely injectivity of its representation. -/
theorem traceExtension_star_mul_self_eq_zero_iff
    (family : RepresentativeShellFamily) (a : ShellFamilyTarget family) :
    traceExtension family (star a * a) = 0 ↔ a = 0 := by
  constructor
  · intro ha
    apply eq_zero_of_apply_star_mul_self_eq_zero_of_tracial
      (traceExtensionPositive family)
      (fun x y ↦ traceExtension_mul_comm family x y)
      (tracialRepresentation family) (tracialVector family)
      (fun x ↦ inner_tracialVector_tracialRepresentation family x)
      (denseRange_tracialRepresentation_orbit family)
      (tracialRepresentation_injective family)
    exact ha
  · rintro rfl
    simp only [star_zero, zero_mul, map_zero]

set_option maxHeartbeats 1000000 in
/-- Every normalized continuous trace on the target restricts to the
original normalized trace on CAR. -/
theorem apply_shellFamilySourceHom_eq_trace_of_apply_one_of_mul_comm
    (family : RepresentativeShellFamily)
    (φ : ShellFamilyTarget family →L[ℂ] ℂ) (hφ1 : φ 1 = 1)
    (hφ : ∀ a b, φ (a * b) = φ (b * a)) (b : Limit) :
    φ (shellFamilySourceHom family b) = trace b := by
  let j := shellFamilySourceHom family
  let ψ : Limit →L[ℂ] ℂ :=
    { toLinearMap := φ.toLinearMap.comp j.toLinearMap
      cont := φ.continuous.comp (map_continuous j) }
  have hψ1 : ψ 1 = 1 := by
    change φ (j 1) = 1
    rw [map_one, hφ1]
  have hψ (a b : Limit) : ψ (a * b) = ψ (b * a) := by
    change φ (j (a * b)) = φ (j (b * a))
    rw [map_mul j, map_mul j]
    exact hφ _ _
  have heq := eq_trace_of_apply_one_of_mul_comm ψ hψ1 hψ
  exact congrArg (fun f : Limit →L[ℂ] ℂ ↦ f b) heq

/-- There is no other tracial state of the target. -/
theorem eq_traceExtension_of_mem_stateSpace_of_mul_comm
    (family : RepresentativeShellFamily)
    (φ : ShellFamilyTarget family →L[ℂ] ℂ)
    (hφ : φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family))
    (hφtrace : ∀ a b, φ (a * b) = φ (b * a)) : φ = traceExtension family := by
  apply eq_traceExtension_of_mem_stateSpace_of_apply_shellFamilySourceHom_eq_trace family φ hφ
  exact apply_shellFamilySourceHom_eq_trace_of_apply_one_of_mul_comm family φ hφ.2 hφtrace

/-- The existing target has exactly one tracial state. Faithfulness is proved
separately above; uniqueness ranges over all states, not just selected extensions. -/
theorem existsUnique_tracial_state (family : RepresentativeShellFamily) :
    ∃! φ : ShellFamilyTarget family →L[ℂ] ℂ,
      φ ∈ MathlibAnnex.Analysis.CStarAlgebra.stateSpace (ShellFamilyTarget family) ∧
        ∀ a b, φ (a * b) = φ (b * a) := by
  refine ⟨traceExtension family,
    ⟨traceExtension_mem_stateSpace family, traceExtension_mul_comm family⟩, ?_⟩
  intro φ hφ
  exact eq_traceExtension_of_mem_stateSpace_of_mul_comm family φ hφ.1 hφ.2

end MathlibAnnex.CStarAlgebra.CAR
