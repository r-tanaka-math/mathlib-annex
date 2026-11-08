import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceWeakClosure
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceHyperfinite

set_option autoImplicit false

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder InnerProduct
open MathlibAnnex.CStarAlgebra.CAR
open MathlibAnnex.Analysis.CStarAlgebra

-- The same selected target and both inclusions, with no analytic premises.
example : traceRepresentation.range ≤ separableCounterexampleRepresentation.range ∧
    separableCounterexampleRepresentation.range ≤ traceVonNeumannAlgebra.toStarSubalgebra :=
  separableCounterexampleRepresentation_range_sandwich

example : Set.centralizer
      (Set.centralizer (Set.range separableCounterexampleRepresentation)) =
    (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) :=
  separableCounterexampleRepresentation_bicommutant_eq

-- Standard SOT and WOT, explicitly on their respective type copies.
example :
    closure ((ContinuousLinearMap.toPointwiseConvergenceCLM
      ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace) ''
      Set.range separableCounterexampleRepresentation) =
    (ContinuousLinearMap.toPointwiseConvergenceCLM
      ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace) ''
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) :=
  closure_sot_traceModelRepresentation_range homogeneityShellFamily

example :
    closure ((ContinuousLinearMapWOT.ofCLM :
      (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) →
      (TraceHilbertSpace →WOT[ℂ] TraceHilbertSpace)) ''
      Set.range separableCounterexampleRepresentation) =
    (ContinuousLinearMapWOT.ofCLM :
      (TraceHilbertSpace →L[ℂ] TraceHilbertSpace) →
      (TraceHilbertSpace →WOT[ℂ] TraceHilbertSpace)) ''
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) :=
  closure_wot_traceModelRepresentation_range homogeneityShellFamily

-- The actual pre-existing sums and adjoint sums are retained together.
example (family : RepresentativeShellFamily)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) :
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum
        (fun n ↦ traceRepresentation ((representativeShellData family i).link n)))
      atTop (traceModelRepresentation family (shellFamilyGenerator family i)) ∧
    ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum
        (fun n ↦ (traceRepresentation ((representativeShellData family i).link n))†))
      atTop ((traceModelRepresentation family (shellFamilyGenerator family i))†) :=
  stronglyConverges_traceRepresentation_shell_sums family i

-- Algebraic infinite-dimensionality and actual finite matrix approximants.
example : ¬ FiniteDimensional ℂ traceVonNeumannAlgebra.toStarSubalgebra ∧
    Monotone traceStageRange ∧
    (∀ n, traceStageRange n ≤ traceVonNeumannAlgebra.toStarSubalgebra) ∧
    (∀ n, FiniteDimensional ℂ (traceStageRange n)) ∧
    (∀ n, Module.finrank ℂ (traceStageRange n) = (2 ^ n) * (2 ^ n)) ∧
    VonNeumannAlgebra.IsHyperfinite traceVonNeumannAlgebra :=
  ⟨not_finiteDimensional_traceVonNeumannAlgebra, traceStageRange_mono,
    traceStageRange_le_traceVonNeumannAlgebra, finiteDimensional_traceStageRange,
    finrank_traceStageRange, isHyperfinite_traceVonNeumannAlgebra⟩

example :
    closure ((ContinuousLinearMap.toPointwiseConvergenceCLM
      ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace) ''
      ⋃ n, (traceStageRange n : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) =
    (ContinuousLinearMap.toPointwiseConvergenceCLM
      ℂ (RingHom.id ℂ) TraceHilbertSpace TraceHilbertSpace) ''
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) :=
  closure_sot_iUnion_traceStageRange

example : traceVonNeumannTrace ∈ @stateSpace traceVonNeumannAlgebra.toStarSubalgebra _ _
      (Subtype.starOrderedRing (𝕜 := ℂ) traceVonNeumannAlgebra.toStarSubalgebra) ∧
    (∀ S T, traceVonNeumannTrace (S * T) = traceVonNeumannTrace (T * S)) ∧
    (∀ T, traceVonNeumannTrace (star T * T) = 0 ↔ T = 0) :=
  ⟨traceVonNeumannTrace_mem_stateSpace, traceVonNeumannTrace_mul_comm,
    traceVonNeumannTrace_star_mul_self_eq_zero_iff⟩
