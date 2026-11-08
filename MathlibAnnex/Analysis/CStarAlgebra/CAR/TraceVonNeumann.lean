import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceFiniteStages
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# The von Neumann algebra of the fixed CAR trace representation

The representation, Hilbert space, and cyclic vector are the existing CAR
objects. The generated von Neumann algebra is formed in this very operator
algebra. Its vector functional therefore extends the original CAR trace.
-/

set_option autoImplicit false

open Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra

/-- The double commutant of CAR in its original trace GNS representation. -/
noncomputable def traceVonNeumannAlgebra : VonNeumannAlgebra TraceHilbertSpace :=
  VonNeumannAlgebra.generated traceRepresentation.range

/-- Every represented CAR element belongs to the same trace von Neumann algebra. -/
theorem traceRepresentation_mem_traceVonNeumannAlgebra (a : Limit) :
    traceRepresentation a ∈ traceVonNeumannAlgebra :=
  VonNeumannAlgebra.subset_generated traceRepresentation.range ⟨a, rfl⟩

/-- The algebra itself is infinite-dimensional: its faithful CAR subalgebra
already is. No inference is made from the dimension of the representation space. -/
theorem not_finiteDimensional_traceVonNeumannAlgebra :
    ¬ FiniteDimensional ℂ traceVonNeumannAlgebra.toStarSubalgebra := by
  apply not_finiteDimensional_of_range_traceRepresentation_le
  exact VonNeumannAlgebra.subset_generated traceRepresentation.range

/-- The CAR trace vector defines a continuous functional on the generated algebra. -/
noncomputable def traceVonNeumannTrace :
    traceVonNeumannAlgebra.toStarSubalgebra →L[ℂ] ℂ :=
  Representation.vectorFunctional traceVonNeumannAlgebra.toStarSubalgebra.subtype traceVector

@[simp]
theorem traceVonNeumannTrace_apply (T : traceVonNeumannAlgebra.toStarSubalgebra) :
    traceVonNeumannTrace T = inner ℂ traceVector (T.1 traceVector) := rfl

/-- Restricting the extended functional along CAR recovers the fixed trace. -/
@[simp]
theorem traceVonNeumannTrace_traceRepresentation (a : Limit) :
    traceVonNeumannTrace
      ⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ = trace a :=
  inner_traceVector_traceRepresentation a

/-- The extended vector functional is a state. -/
theorem traceVonNeumannTrace_mem_stateSpace :
    traceVonNeumannTrace ∈ @stateSpace traceVonNeumannAlgebra.toStarSubalgebra _ _
      (Subtype.starOrderedRing (𝕜 := ℂ) traceVonNeumannAlgebra.toStarSubalgebra) := by
  letI := Subtype.starOrderedRing (𝕜 := ℂ) traceVonNeumannAlgebra.toStarSubalgebra
  exact vectorFunctional_mem_stateSpace traceVonNeumannAlgebra.toStarSubalgebra.subtype
    traceVector norm_traceVector

@[simp]
theorem traceVonNeumannTrace_one : traceVonNeumannTrace 1 = 1 :=
  traceVonNeumannTrace_mem_stateSpace.2

/-- The original CAR orbit already witnesses cyclicity for the larger algebra. -/
theorem denseRange_traceVonNeumannAlgebra_orbit :
    DenseRange (fun T : traceVonNeumannAlgebra.toStarSubalgebra ↦ T.1 traceVector) := by
  apply denseRange_traceRepresentation_orbit.mono
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩, rfl⟩

end MathlibAnnex.CStarAlgebra.CAR
