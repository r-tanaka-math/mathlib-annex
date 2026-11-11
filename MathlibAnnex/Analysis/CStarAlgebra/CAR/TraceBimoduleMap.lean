/-
New source contribution; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceMatrixCompression
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceHyperfinite
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveBimodule
import Mathlib.Topology.ClusterPt

/-!
# A positive CAR bimodule map on the fixed trace Hilbert space

The finite-stage compressions have a single cluster point in the product of
weak operator topologies on the space of all maps. For each fixed matrix
stage, eventual inclusion in the existing closed bimodule-extension family
passes its range, restriction and bimodule equations to this same cluster
point. Positivity supplies norm continuity, and the existing norm density of
the represented matrix stages extends both outer variables to CAR.

The resulting map takes values in the original trace von Neumann algebra.
Only CAR restriction and CAR bimodularity are asserted. No normality, full
von Neumann algebra bimodularity, or type III strengthening is used or claimed.

The closed-family/cluster-point proof route adapts the existing
`TypeI/CommutantRetraction` argument. Its target and eventual constraints are
different here: the range is the trace algebra, not the represented commutant.
The compactness and positive-map recovery APIs are reused without duplication.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.CStarAlgebra.CAR

local notation "Bτ" => TraceHilbertSpace →L[ℂ] TraceHilbertSpace
local notation "Wτ" => TraceHilbertSpace →WOT[ℂ] TraceHilbertSpace

/-- One common pointwise-WOT cluster point of the actual stage compressions
belongs to the existing bimodule-extension family for every fixed stage.
The quantifier over stages lies inside the choice of the single map. -/
theorem exists_mapClusterPt_traceMatrixCompression :
    ∃ f ∈ positiveUnitalMapSet (A := Bτ) (H := TraceHilbertSpace),
      MapClusterPt f (atTop : Filter ℕ)
        (fun n T => ContinuousLinearMapWOT.ofCLM (traceMatrixCompression n T)) ∧
      ∀ m : ℕ, f ∈ positiveBimoduleExtensionSet (traceStageRange m)
        traceVonNeumannAlgebra
        (StarSubalgebra.inclusion (traceStageRange_le_traceVonNeumannAlgebra m)) := by
  let P (n : ℕ) : Bτ →P[ℂ] Bτ :=
    PositiveContinuousLinearMap.ofClass (traceMatrixCompression n)
  have hPone (n : ℕ) : P n 1 = 1 := traceMatrixCompression_one n
  obtain ⟨f, hf, hcluster⟩ := exists_mapClusterPt_positiveUnitalMapSet
    (atTop : Filter ℕ) P hPone
  refine ⟨f, hf, hcluster, ?_⟩
  intro m
  apply (isClosed_positiveBimoduleExtensionSet (traceStageRange m)
    traceVonNeumannAlgebra
    (StarSubalgebra.inclusion (traceStageRange_le_traceVonNeumannAlgebra m))).mem_of_mapClusterPt hcluster
  apply Filter.eventually_atTop.2
  refine ⟨m, ?_⟩
  intro n hmn
  refine ⟨mem_positiveUnitalMapSet (P n) (hPone n), ?_, ?_, ?_⟩
  · intro T
    exact traceStageRange_le_traceVonNeumannAlgebra n
      (traceMatrixCompression_mem_traceStageRange n T)
  · intro d
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (traceMatrixCompression_of_mem n (d : Bτ)
        (traceStageRange_mono hmn d.property))
  · intro d e T
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (traceMatrixCompression_mul_mul n (d : Bτ) (e : Bτ) T
        (traceStageRange_mono hmn d.property)
        (traceStageRange_mono hmn e.property))

/-- A positive unital map into the actual CAR trace von Neumann algebra,
fixing represented CAR and satisfying its two-sided bimodule identity.
No auxiliary map is an input to this existence theorem. -/
theorem exists_traceBimoduleMap :
    ∃ E : Bτ →ₚ[ℂ] traceVonNeumannAlgebra.toStarSubalgebra,
      E 1 = 1 ∧
      (∀ a : Limit, E (traceRepresentation a) =
        ⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩) ∧
      ∀ (a b : Limit) (T : Bτ),
        E (traceRepresentation a * T * traceRepresentation b) =
          (⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
            traceVonNeumannAlgebra.toStarSubalgebra) * E T *
          ⟨traceRepresentation b, traceRepresentation_mem_traceVonNeumannAlgebra b⟩ := by
  obtain ⟨f, hf, _hcluster, hstage⟩ := exists_mapClusterPt_traceMatrixCompression
  let P : Bτ →P[ℂ] Bτ := positiveUnitalMapOfMem f hf
  have hPcont : Continuous P := P.toContinuousLinearMap.continuous
  have hR (T : Bτ) : (f T).toCLM ∈ traceVonNeumannAlgebra :=
    (hstage 0).2.1 T
  have hfix_stage (m : ℕ) (a : Bτ) (ha : a ∈ traceStageRange m) : P a = a := by
    exact congrArg ContinuousLinearMapWOT.toCLM
      ((hstage m).2.2.1 ⟨a, ha⟩)
  have hbi_stage (m : ℕ) (a b T : Bτ)
      (ha : a ∈ traceStageRange m) (hb : b ∈ traceStageRange m) :
      P (a * T * b) = a * P T * b := by
    exact congrArg ContinuousLinearMapWOT.toCLM
      ((hstage m).2.2.2 ⟨a, ha⟩ ⟨b, hb⟩ T)
  have hfix (a : Limit) : P (traceRepresentation a) = traceRepresentation a := by
    have hclosed : IsClosed {S : Bτ | P S = S} :=
      isClosed_eq hPcont continuous_id
    apply closure_minimal ?_ hclosed
      (traceRepresentation_mem_closure_iUnion_traceStageRange a)
    intro S hS
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hS
    exact hfix_stage m S hm
  have hleft (m : ℕ) (b : Bτ) (hb : b ∈ traceStageRange m)
      (a : Limit) (T : Bτ) :
      P (traceRepresentation a * T * b) = traceRepresentation a * P T * b := by
    have hclosed : IsClosed {S : Bτ | P (S * T * b) = S * P T * b} :=
      isClosed_eq (hPcont.comp ((continuous_id.mul continuous_const).mul continuous_const))
        ((continuous_id.mul continuous_const).mul continuous_const)
    apply closure_minimal ?_ hclosed
      (traceRepresentation_mem_closure_iUnion_traceStageRange a)
    intro S hS
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hS
    exact hbi_stage (max k m) S b T
      (traceStageRange_mono (le_max_left k m) hk)
      (traceStageRange_mono (le_max_right k m) hb)
  have hbi (a b : Limit) (T : Bτ) :
      P (traceRepresentation a * T * traceRepresentation b) =
        traceRepresentation a * P T * traceRepresentation b := by
    have hclosed : IsClosed {S : Bτ |
        P (traceRepresentation a * T * S) = traceRepresentation a * P T * S} :=
      isClosed_eq (hPcont.comp (continuous_const.mul continuous_id))
        (continuous_const.mul continuous_id)
    apply closure_minimal ?_ hclosed
      (traceRepresentation_mem_closure_iUnion_traceStageRange b)
    intro S hS
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hS
    exact hleft m S hm a T
  let D := traceRepresentation.range
  have hD : D ≤ traceVonNeumannAlgebra.toStarSubalgebra := by
    rintro T ⟨a, rfl⟩
    exact traceRepresentation_mem_traceVonNeumannAlgebra a
  let sigma : D →⋆ₐ[ℂ] traceVonNeumannAlgebra.toStarSubalgebra :=
    StarSubalgebra.inclusion hD
  have hfamily : f ∈ positiveBimoduleExtensionSet D traceVonNeumannAlgebra sigma := by
    refine ⟨hf, hR, ?_, ?_⟩
    · intro d
      apply ContinuousLinearMapWOT.toCLM_injective
      change P (d : Bτ) = (d : Bτ)
      obtain ⟨a, ha⟩ := d.property
      rw [← ha]
      exact hfix a
    · intro d e T
      apply ContinuousLinearMapWOT.toCLM_injective
      change P ((d : Bτ) * T * (e : Bτ)) = (d : Bτ) * P T * (e : Bτ)
      obtain ⟨a, ha⟩ := d.property
      obtain ⟨b, hb⟩ := e.property
      rw [← ha, ← hb]
      exact hbi a b T
  refine ⟨(positiveBimoduleExtensionOfMem D traceVonNeumannAlgebra sigma f hfamily).toPositiveLinearMap, ?_, ?_, ?_⟩
  · exact positiveBimoduleExtensionOfMem_one D traceVonNeumannAlgebra sigma f hfamily
  · intro a
    apply Subtype.ext
    change P (traceRepresentation a) = traceRepresentation a
    exact hfix a
  · intro a b T
    apply Subtype.ext
    change P (traceRepresentation a * T * traceRepresentation b) =
      traceRepresentation a * P T * traceRepresentation b
    exact hbi a b T

/-- The actual map selected from the proved finite-stage/compactness existence
theorem, on the original Hilbert space and with values in the original R. -/
def traceBimoduleMap : Bτ →ₚ[ℂ] traceVonNeumannAlgebra.toStarSubalgebra :=
  exists_traceBimoduleMap.choose

@[simp]
theorem traceBimoduleMap_one : traceBimoduleMap 1 = 1 :=
  exists_traceBimoduleMap.choose_spec.1

/-- The constructed map fixes the represented CAR algebra. -/
@[simp]
theorem traceBimoduleMap_traceRepresentation (a : Limit) :
    traceBimoduleMap (traceRepresentation a) =
      ⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :=
  exists_traceBimoduleMap.choose_spec.2.1 a

/-- Both outer variables range over CAR, with an arbitrary bounded operator
in the middle. This is the exact auxiliary-map identity used by the trace test. -/
theorem traceBimoduleMap_mul_mul (a b : Limit) (T : Bτ) :
    traceBimoduleMap (traceRepresentation a * T * traceRepresentation b) =
      (⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
        traceVonNeumannAlgebra.toStarSubalgebra) * traceBimoduleMap T *
      ⟨traceRepresentation b, traceRepresentation_mem_traceVonNeumannAlgebra b⟩ :=
  exists_traceBimoduleMap.choose_spec.2.2 a b T

end MathlibAnnex.CStarAlgebra.CAR
