import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceFiniteStages

set_option autoImplicit false

open MathlibAnnex.CStarAlgebra.CAR

noncomputable example (n : ℕ) : Stage n ≃⋆ₐ[ℂ] traceStageRange n := traceStageEquiv n

example (n : ℕ) : FiniteDimensional ℂ (traceStageRange n) :=
  finiteDimensional_traceStageRange n

example (n : ℕ) :
    (1 : TraceHilbertSpace →L[ℂ] TraceHilbertSpace) ∈ traceStageRange n :=
  (traceStageRange n).one_mem

example (n m : ℕ) (hnm : n ≤ m) : traceStageRange n ≤ traceStageRange m :=
  traceStageRange_mono hnm

example (a : Limit) : traceRepresentation a ∈ closure
    (⋃ n, (traceStageRange n : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace))) :=
  traceRepresentation_mem_closure_iUnion_traceStageRange a

example : ¬ FiniteDimensional ℂ traceRepresentation.range :=
  not_finiteDimensional_of_range_traceRepresentation_le traceRepresentation.range le_rfl

example (n : ℕ) : Module.finrank ℂ (traceStageRange n) = (2 ^ n) * (2 ^ n) :=
  finrank_traceStageRange n
