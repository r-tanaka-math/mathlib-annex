import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceWeakClosure
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceHyperfinite
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceUnique
import MathlibAnnex.Analysis.VonNeumannAlgebra.NormalFunctional
import MathlibAnnex.Analysis.VonNeumannAlgebra.Factor
import MathlibAnnex.Analysis.VonNeumannAlgebra.Finite
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1

/-!
# The fixed CAR trace algebra is a hyperfinite finite infinite-dimensional factor

The general normal-vector-functional, unique-trace factor, and finite-unit
criteria are applied to the original CAR representation and trace vector.
All their mathematical hypotheses are supplied by named CAR proofs. The
infinite-dimensionality concerns the algebra itself.
-/

set_option autoImplicit false

open Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.TensorAveraging

/-- Normality is the directed positive-supremum notion on this same algebra. -/
theorem isNormalPositiveFunctional_traceVonNeumannTrace :
    VonNeumannAlgebra.IsNormalPositiveFunctional
      traceVonNeumannAlgebra traceVonNeumannTrace := by
  simpa only [traceVonNeumannTrace] using
    VonNeumannAlgebra.isNormalPositiveFunctional_vectorFunctional
      traceVonNeumannAlgebra traceVector

/-- Uniqueness of the normalized continuous CAR trace forces scalar center
in its cyclic weak closure. -/
theorem isFactor_traceVonNeumannAlgebra :
    VonNeumannAlgebra.IsFactor traceVonNeumannAlgebra := by
  refine VonNeumannAlgebra.isFactor_of_unique_trace_of_wotDense
    (M := traceVonNeumannAlgebra) (π := traceRepresentation)
    (ξ := traceVector) (hξ := norm_traceVector)
    (hπ := traceRepresentation_mem_traceVonNeumannAlgebra) (hdense := ?_)
    (hcyclic := denseRange_traceRepresentation_orbit) (τ := trace)
    (hτ := fun a ↦ (inner_traceVector_traceRepresentation a).symm)
    (hτone := trace_one) (hτtrace := trace_mul_comm)
    (hunique := eq_trace_of_apply_one_of_mul_comm)
  intro T hT
  have h := (VonNeumannAlgebra.mem_generated_iff_mem_wotClosure traceRepresentation.range T).mp hT
  change ContinuousLinearMapWOT.ofCLM T ∈ closure
    (ContinuousLinearMapWOT.ofCLM '' Set.range traceRepresentation) at h
  simpa only [← Set.range_comp, Function.comp_def] using h

/-- The faithful tracial state makes the unit finite in the isometry sense. -/
theorem isFinite_traceVonNeumannAlgebra :
    VonNeumannAlgebra.IsFinite traceVonNeumannAlgebra := by
  let φ := (operatorVectorState TraceHilbertSpace traceVector).toLinearMap
  have hrestrict (T : traceVonNeumannAlgebra.toStarSubalgebra) :
      φ T.val = traceVonNeumannTrace T := rfl
  apply VonNeumannAlgebra.isFinite_of_faithful_tracial traceVonNeumannAlgebra φ
  · intro a ha b hb
    let S : traceVonNeumannAlgebra.toStarSubalgebra := ⟨a, ha⟩
    let T : traceVonNeumannAlgebra.toStarSubalgebra := ⟨b, hb⟩
    exact (hrestrict (S * T)).trans
      ((traceVonNeumannTrace_mul_comm S T).trans (hrestrict (T * S)).symm)
  · intro a ha h
    let T : traceVonNeumannAlgebra.toStarSubalgebra := ⟨a, ha⟩
    have hT := (traceVonNeumannTrace_star_mul_self_eq_zero_iff T).mp
      ((hrestrict (star T * T)).symm.trans h)
    exact congrArg Subtype.val hT

/-- The fixed CAR trace double commutant is a type II₁ factor. -/
theorem isTypeII1_traceVonNeumannAlgebra :
    VonNeumannAlgebra.IsTypeII1 traceVonNeumannAlgebra :=
  ⟨isFactor_traceVonNeumannAlgebra, isFinite_traceVonNeumannAlgebra,
    not_finiteDimensional_traceVonNeumannAlgebra⟩

end MathlibAnnex.CStarAlgebra.CAR
