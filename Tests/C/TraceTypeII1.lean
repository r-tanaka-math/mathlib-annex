import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceTypeII1
import MathlibAnnex.Analysis.CStarAlgebra.CAR.HilbertBasisConsequences

set_option autoImplicit false

open Set
open scoped CStarAlgebra ComplexOrder InnerProduct
open MathlibAnnex.CStarAlgebra.CAR
open MathlibAnnex.Analysis.CStarAlgebra

-- Use the standard pre-GNS seminorm when elaborating the fixed-model conjunction.
private noncomputable local instance tracePreGNSSeminorm : SeminormedAddCommGroup tracePositive.PreGNS :=
  PositiveLinearMap.instSeminormedAddCommGroupPreGNS tracePositive

-- The fixed closure, faithful normal trace, factor, finite unit, algebraic
-- infinite-dimensionality and actual hyperfinite approximation are consumed
-- together without an extra trace, density, or factor assumption.
example :
    traceRepresentation.range ≤ separableCounterexampleRepresentation.range ∧
    separableCounterexampleRepresentation.range ≤ traceVonNeumannAlgebra.toStarSubalgebra ∧
    Set.centralizer (Set.centralizer (Set.range separableCounterexampleRepresentation)) =
      (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) ∧
    traceVonNeumannTrace ∈ @stateSpace traceVonNeumannAlgebra.toStarSubalgebra _ _
      (Subtype.starOrderedRing (𝕜 := ℂ) traceVonNeumannAlgebra.toStarSubalgebra) ∧
    VonNeumannAlgebra.IsNormalPositiveFunctional traceVonNeumannAlgebra traceVonNeumannTrace ∧
    (∀ S T, traceVonNeumannTrace (S * T) = traceVonNeumannTrace (T * S)) ∧
    (∀ T, traceVonNeumannTrace (star T * T) = 0 ↔ T = 0) ∧
    VonNeumannAlgebra.IsFactor traceVonNeumannAlgebra ∧
    VonNeumannAlgebra.IsFinite traceVonNeumannAlgebra ∧
    ¬ FiniteDimensional ℂ traceVonNeumannAlgebra.toStarSubalgebra ∧
    VonNeumannAlgebra.IsTypeII1 traceVonNeumannAlgebra ∧
    VonNeumannAlgebra.IsHyperfinite traceVonNeumannAlgebra ∧
    Nonempty (HilbertBasis ℕ ℂ TraceHilbertSpace) :=
  ⟨separableCounterexampleRepresentation_range_sandwich.1,
    separableCounterexampleRepresentation_range_sandwich.2,
    separableCounterexampleRepresentation_bicommutant_eq,
    traceVonNeumannTrace_mem_stateSpace,
    isNormalPositiveFunctional_traceVonNeumannTrace,
    traceVonNeumannTrace_mul_comm, traceVonNeumannTrace_star_mul_self_eq_zero_iff,
    isFactor_traceVonNeumannAlgebra, isFinite_traceVonNeumannAlgebra,
    not_finiteDimensional_traceVonNeumannAlgebra,
    isTypeII1_traceVonNeumannAlgebra, isHyperfinite_traceVonNeumannAlgebra,
    nonempty_hilbertBasis_nat_traceHilbertSpace⟩

-- The finite-unit predicate is also consumed in its direct operator meaning.
example (v : TraceHilbertSpace →L[ℂ] TraceHilbertSpace)
    (hv : v ∈ traceVonNeumannAlgebra) (hisometry : star v * v = 1) :
    v * star v = 1 :=
  isFinite_traceVonNeumannAlgebra v hv hisometry

-- Scalar center and a nonzero unit, written without the factor predicate.
example : (1 : TraceHilbertSpace →L[ℂ] TraceHilbertSpace) ≠ 0 ∧
    ∀ T : TraceHilbertSpace →L[ℂ] TraceHilbertSpace,
      T ∈ traceVonNeumannAlgebra →
      T ∈ Set.centralizer
        (traceVonNeumannAlgebra : Set (TraceHilbertSpace →L[ℂ] TraceHilbertSpace)) →
      ∃ c : ℂ, T = c • (1 : TraceHilbertSpace →L[ℂ] TraceHilbertSpace) :=
  isFactor_traceVonNeumannAlgebra

-- The same supremum in R realizes the supremum of the real trace values.
private theorem exists_isLUB_traceVonNeumannTrace_re (s : Set traceVonNeumannAlgebra.toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ x ∈ s, 0 ≤ x) (hbdd : BddAbove s) :
    ∃ a, IsLUB s a ∧
      IsLUB ((fun x ↦ (traceVonNeumannTrace x).re) '' s) (traceVonNeumannTrace a).re := by
  obtain ⟨a, _, ha, _⟩ := traceVonNeumannAlgebra.exists_isLUB_stronglyConverges
    s hne hdir hpos hbdd
  exact ⟨a, ha, isNormalPositiveFunctional_traceVonNeumannTrace.2 s hne hdir hpos hbdd a ha⟩
