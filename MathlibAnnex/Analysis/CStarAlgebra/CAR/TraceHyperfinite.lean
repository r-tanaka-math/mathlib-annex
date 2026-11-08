import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceVonNeumann
import MathlibAnnex.Analysis.VonNeumannAlgebra.Hyperfinite
import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant

/-!
# Finite matrix approximations of the same CAR trace von Neumann algebra

The finite stages are the represented copies of the actual CAR matrix
algebras. Norm density in the represented CAR image and the bicommutant
theorem give strong density in its von Neumann closure.
-/

set_option autoImplicit false

open Set Topology

namespace MathlibAnnex.CStarAlgebra.CAR

local notation "toSOT" => ContinuousLinearMap.toPointwiseConvergenceCLM
  ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace

/-- Each represented matrix stage is a unital star subalgebra of the same R. -/
theorem traceStageRange_le_traceVonNeumannAlgebra (n : ℕ) :
    traceStageRange n ≤ traceVonNeumannAlgebra.toStarSubalgebra := by
  intro T hT
  exact VonNeumannAlgebra.subset_generated traceRepresentation.range
    (traceStageRange_le_range n hT)

/-- The increasing finite-dimensional matrix stages have strongly dense union
in the CAR trace von Neumann algebra. -/
theorem closure_sot_iUnion_traceStageRange :
    closure (toSOT '' ⋃ n, (traceStageRange n :
      Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) =
    toSOT '' (traceVonNeumannAlgebra :
      Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
  have hCAR : closure (toSOT '' Set.range traceRepresentation) =
      toSOT '' (traceVonNeumannAlgebra :
        Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) := by
    apply Set.Subset.antisymm
    · intro T hT
      exact ⟨T, (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure
        traceRepresentation.range T).mpr hT, rfl⟩
    · rintro _ ⟨T, hT, rfl⟩
      exact (VonNeumannAlgebra.mem_generated_iff_mem_sotClosure
        traceRepresentation.range T).mp hT
  have hsubset :
      toSOT '' (⋃ n, (traceStageRange n :
        Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) ⊆
      toSOT '' Set.range traceRepresentation := by
    rintro _ ⟨T, hT, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hT
    exact ⟨T, traceStageRange_le_range n hn, rfl⟩
  have happrox : toSOT '' Set.range traceRepresentation ⊆
      closure (toSOT '' ⋃ n, (traceStageRange n :
        Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact image_closure_subset_closure_image (toSOT).continuous
      ⟨traceRepresentation a,
        traceRepresentation_mem_closure_iUnion_traceStageRange a, rfl⟩
  calc
    _ = closure (toSOT '' Set.range traceRepresentation) :=
      Set.Subset.antisymm (closure_mono hsubset)
        (closure_minimal happrox isClosed_closure)
    _ = _ := hCAR

/-- The fixed CAR trace double commutant is hyperfinite, witnessed by its
actual increasing finite matrix stages. -/
theorem isHyperfinite_traceVonNeumannAlgebra :
    VonNeumannAlgebra.IsHyperfinite traceVonNeumannAlgebra :=
  VonNeumannAlgebra.isHyperfinite_of_monotone traceVonNeumannAlgebra traceStageRange
    traceStageRange_mono traceStageRange_le_traceVonNeumannAlgebra
    finiteDimensional_traceStageRange closure_sot_iUnion_traceStageRange

end MathlibAnnex.CStarAlgebra.CAR
