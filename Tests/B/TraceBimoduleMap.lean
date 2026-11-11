/-
New typed consumers; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceBimoduleMap

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.CStarAlgebra.CAR
open scoped CStarAlgebra ComplexOrder

local notation "Bτ" => TraceHilbertSpace →L[ℂ] TraceHilbertSpace

-- The same f is a cluster point of the whole map sequence and satisfies
-- every finite-stage family condition. No subsequence or separability input.
example :
    ∃ f ∈ positiveUnitalMapSet (A := Bτ) (H := TraceHilbertSpace),
      MapClusterPt f (atTop : Filter ℕ)
        (fun n T => ContinuousLinearMapWOT.ofCLM (traceMatrixCompression n T)) ∧
      ∀ m : ℕ, f ∈ positiveBimoduleExtensionSet (traceStageRange m)
        traceVonNeumannAlgebra
        (StarSubalgebra.inclusion (traceStageRange_le_traceVonNeumannAlgebra m)) := by
  exact exists_mapClusterPt_traceMatrixCompression

-- This term has the literal codomain required by the previous trace test.
example : Bτ →ₚ[ℂ] traceVonNeumannAlgebra.toStarSubalgebra := traceBimoduleMap

private theorem map_smul_add {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K)
    (f : (K →L[ℂ] K) →ₚ[ℂ] M.toStarSubalgebra) (c : ℂ) (S T : K →L[ℂ] K) :
    f (c • S + T) = c • f S + f T := by rw [map_add, map_smul]

example (c : ℂ) (S T : Bτ) :=
  map_smul_add (K := TraceHilbertSpace) traceVonNeumannAlgebra traceBimoduleMap c S T

example : traceBimoduleMap 1 = 1 := traceBimoduleMap_one

example (T : Bτ) (hT : 0 ≤ T) : 0 ≤ traceBimoduleMap T := by
  exact traceBimoduleMap.map_nonneg hT

example (a : Limit) :
    traceBimoduleMap (traceRepresentation a) =
      ⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ := by
  exact traceBimoduleMap_traceRepresentation a

example (a b : Limit) (T : Bτ) :
    traceBimoduleMap (traceRepresentation a * T * traceRepresentation b) =
      (⟨traceRepresentation a, traceRepresentation_mem_traceVonNeumannAlgebra a⟩ :
        traceVonNeumannAlgebra.toStarSubalgebra) * traceBimoduleMap T *
      ⟨traceRepresentation b, traceRepresentation_mem_traceVonNeumannAlgebra b⟩ := by
  exact traceBimoduleMap_mul_mul a b T

-- Norm continuity comes from the existing positive-map class instance,
-- and asserts no normality in a von Neumann algebra topology.
private theorem continuous_into_vn {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (M : VonNeumannAlgebra K)
    (f : (K →L[ℂ] K) →ₚ[ℂ] M.toStarSubalgebra) : Continuous f := by
  let g : (K →L[ℂ] K) →ₚ[ℂ] (K →L[ℂ] K) := PositiveLinearMap.mk₀
    (M.toStarSubalgebra.subtype.toLinearMap.comp f.toLinearMap) (fun T hT ↦ f.map_nonneg hT)
  exact continuous_induced_rng.mpr (map_continuous g)

example : Continuous traceBimoduleMap :=
  continuous_into_vn (K := TraceHilbertSpace) traceVonNeumannAlgebra traceBimoduleMap

example (T : Bτ) :
    (traceBimoduleMap T : Bτ) ∈ traceVonNeumannAlgebra := by
  exact (traceBimoduleMap T).property
