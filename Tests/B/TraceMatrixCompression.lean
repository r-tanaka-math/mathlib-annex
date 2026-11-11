/- New typed consumers of the actual finite-stage compression construction.
Source-only handoff: Lean, elaboration and kernel checking are NOT_RUN. -/
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceMatrixCompression

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProduct
open MathlibAnnex.CStarAlgebra.CAR

local notation "Hτ" => TraceHilbertSpace
local notation "Bτ" => Hτ →L[ℂ] Hτ

example (n : ℕ) : ∃ ξ : Hτ,
    traceStageMatrixUnit n 0 0 ξ = ξ ∧ ‖ξ‖ = 1 :=
  exists_unit_fixed_traceStageMatrixUnit n

example (n : ℕ) (i j k l : Fin (2 ^ n)) :
    traceStageMatrixUnit n i j * traceStageMatrixUnit n k l =
      if j = k then traceStageMatrixUnit n i l else 0 :=
  traceStageMatrixUnit_mul n i j k l

example (n : ℕ) (i j : Fin (2 ^ n)) :
    inner ℂ (traceStageVector n i) (traceStageVector n j) =
      if i = j then 1 else 0 := inner_traceStageVector n i j

example (n : ℕ) : EuclideanSpace ℂ (Fin (2 ^ n)) →ₗᵢ[ℂ] Hτ :=
  traceStageIsometry n

example (n : ℕ) :
    (traceStageIsometry n).toContinuousLinearMap.adjoint.comp
      (traceStageIsometry n).toContinuousLinearMap = 1 :=
  (traceStageIsometry n).adjoint_comp_self

example (n : ℕ) (a : Stage n) :
    (traceStageRepresentation n a).comp (traceStageIsometry n).toContinuousLinearMap =
      (traceStageIsometry n).toContinuousLinearMap.comp (traceStageOperatorEquiv n a) :=
  traceStageRepresentation_comp_isometry n a

example (n : ℕ) : Bτ →ₚ[ℂ] Bτ := traceMatrixCompression n

example (n : ℕ) : traceMatrixCompression n 1 = 1 := traceMatrixCompression_one n

example (n : ℕ) (T : Bτ) (hT : 0 ≤ T) : 0 ≤ traceMatrixCompression n T :=
  (traceMatrixCompression n).map_nonneg hT

example (n : ℕ) (T : Bτ) : traceMatrixCompression n T ∈ traceStageRange n :=
  traceMatrixCompression_mem_traceStageRange n T

example (n : ℕ) (a : Bτ) (ha : a ∈ traceStageRange n) :
    traceMatrixCompression n a = a := traceMatrixCompression_of_mem n a ha

example (n : ℕ) (a b T : Bτ)
    (ha : a ∈ traceStageRange n) (hb : b ∈ traceStageRange n) :
    traceMatrixCompression n (a * T * b) = a * traceMatrixCompression n T * b :=
  traceMatrixCompression_mul_mul n a b T ha hb

example (m n : ℕ) (hmn : m ≤ n) (a b T : Bτ)
    (ha : a ∈ traceStageRange m) (hb : b ∈ traceStageRange m) :
    traceMatrixCompression n (a * T * b) = a * traceMatrixCompression n T * b :=
  traceMatrixCompression_mul_mul n a b T
    (traceStageRange_mono hmn ha) (traceStageRange_mono hmn hb)

example (n : ℕ) (T : Bτ) : ‖traceMatrixCompression n T‖ ≤ ‖T‖ :=
  norm_traceMatrixCompression_le n T

example (n : ℕ) : Continuous (traceMatrixCompression n) :=
  continuous_traceMatrixCompression n

example (T : Bτ) : traceMatrixCompression 0 T ∈ traceStageRange 0 :=
  traceMatrixCompression_mem_traceStageRange 0 T
