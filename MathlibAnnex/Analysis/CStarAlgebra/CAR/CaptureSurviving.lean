import MathlibAnnex.Analysis.CStarAlgebra.CAR.CaptureZero
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Vectors carried by a surviving completed-CAR defect

The target-side unitary-completion relation transports a normalized vector
from a nonzero initial limiting fixed space to the root limiting fixed space.
The actual completed-CAR compression estimates then identify both vector
states.  No ambient rank-one assertion is made for an arbitrary target
representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter Topology
open scoped ComplexOrder ENNReal lp InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

universe v

/-- A specified nonzero limiting fixed space supplies unit vectors carrying
the selected state and the root state, joined by the represented target
generator. -/
theorem exists_targetDefectVectors_of_fixedSpace_ne_bot
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit)
    (hi : (⨅ n, ((restrictedRepresentation L rho)
      (transportedFlag family i n)).range) ≠ ⊥) :
    ∃ eta_i eta_o : K,
      ‖eta_i‖ = 1 ∧ ‖eta_o‖ = 1 ∧
      (∀ n, (restrictedRepresentation L rho)
        (transportedFlag family i n) eta_i = eta_i) ∧
      (∀ n, (restrictedRepresentation L rho) (rootFlag n) eta_o = eta_o) ∧
      (Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) eta_i = eta_o ∧
      Representation.vectorFunctional (restrictedRepresentation L rho) eta_i =
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 ∧
      Representation.vectorFunctional (restrictedRepresentation L rho) eta_o =
        rootState := by
  let sigma := restrictedRepresentation L rho
  let U : ℕ → Submodule ℂ K := fun n ↦
    (sigma (transportedFlag family i n)).range
  let V : ℕ → Submodule ℂ K := fun n ↦ (sigma (rootFlag n)).range
  obtain ⟨S, T, P, Q, R, -, -, -, -, -, -, hPrange, -, hQrange, -, -, -, -,
      -, -, -, htransport⟩ :=
    exists_targetShellReconstruction family L hLunit hLsource rho i
  have hU_ne : (⨅ n, U n) ≠ ⊥ := by
    simpa [U, sigma] using hi
  obtain ⟨x, hxU, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU_ne
  let eta_i : K := NormedSpace.normalize x
  have heta_i_norm : ‖eta_i‖ = 1 := NormedSpace.norm_normalize hxne
  have heta_i_mem : eta_i ∈ ⨅ n, U n := by
    change NormedSpace.normalize x ∈ ⨅ n, U n
    rw [NormedSpace.normalize]
    exact (⨅ n, U n).smul_mem (‖x‖⁻¹ : ℝ) hxU
  let e : K ≃ₗᵢ[ℂ] K := Unitary.linearIsometryEquiv
    (representedGeneratorUnitary L hLunit rho i)
  let eta_o : K := e eta_i
  have heta_o_norm : ‖eta_o‖ = 1 := by
    rw [show ‖eta_o‖ = ‖eta_i‖ by exact e.norm_map eta_i]
    exact heta_i_norm
  have heta_o_mem : eta_o ∈ ⨅ n, V n := by
    exact (htransport eta_i).1 heta_i_mem
  have heta_i_fixed (n : ℕ) :
      sigma (transportedFlag family i n) eta_i = eta_i := by
    have hn : eta_i ∈ U n := (Submodule.mem_iInf U).mp heta_i_mem n
    exact LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (IsStarProjection.map_representation sigma
          (isStarProjection_transportedFlag family i n)).isIdempotentElem) |>.mp hn
  have heta_o_fixed (n : ℕ) : sigma (rootFlag n) eta_o = eta_o := by
    have hn : eta_o ∈ V n := (Submodule.mem_iInf V).mp heta_o_mem n
    exact LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (IsStarProjection.map_representation sigma
          (isStarProjection_rootFlag n)).isIdempotentElem) |>.mp hn
  have heta_i_state : Representation.vectorFunctional sigma eta_i =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 := by
    apply ContinuousLinearMap.ext
    intro b
    have hcoeff := inner_map_eq_of_compression_tendsto sigma
      (Representation.continuousLinearMap sigma).continuous
      (transportedFlag family i)
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 b eta_i eta_i
      (fun n ↦ (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq)
      heta_i_fixed heta_i_fixed
      (tendsto_representative_transported_compression family i b)
    have hself : inner ℂ eta_i eta_i = 1 := by
      rw [inner_self_eq_norm_sq_to_K, heta_i_norm]
      norm_num
    change inner ℂ eta_i (sigma b eta_i) =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 b
    calc
      inner ℂ eta_i (sigma b eta_i) =
          (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 b *
            inner ℂ eta_i eta_i := hcoeff
      _ = (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 b := by
        rw [hself, mul_one]
  have heta_o_state : Representation.vectorFunctional sigma eta_o = rootState := by
    apply ContinuousLinearMap.ext
    intro b
    have hcompression : Tendsto
        (fun n ↦ rootFlag n * b * rootFlag n - rootState b • rootFlag n)
        atTop (nhds 0) := by
      simpa using tendsto_transported_compressionError
        (StarAlgEquiv.refl ℂ Limit) rootState (fun _ ↦ rfl) b
    have hcoeff := inner_map_eq_of_compression_tendsto sigma
      (Representation.continuousLinearMap sigma).continuous rootFlag rootState
      b eta_o eta_o
      (fun n ↦ (isStarProjection_rootFlag n).isSelfAdjoint.star_eq)
      heta_o_fixed heta_o_fixed hcompression
    have hself : inner ℂ eta_o eta_o = 1 := by
      rw [inner_self_eq_norm_sq_to_K, heta_o_norm]
      norm_num
    change inner ℂ eta_o (sigma b eta_o) = rootState b
    calc
      inner ℂ eta_o (sigma b eta_o) =
          rootState b * inner ℂ eta_o eta_o := hcoeff
      _ = rootState b := by rw [hself, mul_one]
  exact ⟨eta_i, eta_o, heta_i_norm, heta_o_norm,
    heta_i_fixed, heta_o_fixed, rfl, heta_i_state, heta_o_state⟩

/-- Every irreducible target representation contains a transported pair of
unit defect vectors with the exact selected and root completed-CAR states. -/
theorem exists_targetDefectVectors
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    ∃ (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) (eta_i eta_o : K),
      ‖eta_i‖ = 1 ∧ ‖eta_o‖ = 1 ∧
      (∀ n, (restrictedRepresentation L rho)
        (transportedFlag family i n) eta_i = eta_i) ∧
      (∀ n, (restrictedRepresentation L rho) (rootFlag n) eta_o = eta_o) ∧
      (Unitary.linearIsometryEquiv
        (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) eta_i = eta_o ∧
      Representation.vectorFunctional (restrictedRepresentation L rho) eta_i =
        (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 ∧
      Representation.vectorFunctional (restrictedRepresentation L rho) eta_o =
        rootState := by
  obtain ⟨i, hi⟩ := exists_nonzero_targetFixedSpace
    family L hLunit hLsource rho hrho
  obtain ⟨eta_i, eta_o, h⟩ :=
    exists_targetDefectVectors_of_fixedSpace_ne_bot
      family L hLunit hLsource rho i hi
  exact ⟨i, eta_i, eta_o, h⟩

/-- A surviving defect yields one common root unit vector and a compatible
unit defect vector for every selected pure-state class.  Each represented
generator sends its selected vector to the same root vector, and every vector
state is identified from the actual completed-CAR compression theorem. -/
theorem exists_targetDefectVectorFamily
    (family : RepresentativeShellFamily)
    (L : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit →
      MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState)
    (hLunit : ∀ i, L i ∈ unitary
      (MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState →L[ℂ]
        MathlibAnnex.CStarAlgebra.PureState.SelectedAtomicHilbert completedRootPureState))
    (hLsource : ∀ i n, (L i).comp (selectedAtomicRepresentation
      (transportedFlag family i n - transportedFlag family i (n + 1))) =
        representedShellLink family i n)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (rho : Representation (AtomicTarget L) K)
    (hrho : rho.IsIrreducible) :
    ∃ (eta_o : K) (eta : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit → K),
      ‖eta_o‖ = 1 ∧
      (∀ n, (restrictedRepresentation L rho) (rootFlag n) eta_o = eta_o) ∧
      Representation.vectorFunctional (restrictedRepresentation L rho) eta_o =
        rootState ∧
      ∀ i,
        ‖eta i‖ = 1 ∧
        (∀ n, (restrictedRepresentation L rho)
          (transportedFlag family i n) (eta i) = eta i) ∧
        (Unitary.linearIsometryEquiv
          (representedGeneratorUnitary L hLunit rho i) : K ≃ₗᵢ[ℂ] K) (eta i) =
            eta_o ∧
        Representation.vectorFunctional (restrictedRepresentation L rho) (eta i) =
          (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 := by
  obtain ⟨i₀, eta₀, eta_o, -, heta_o_norm, -, heta_o_fixed, -, -,
      heta_o_state⟩ :=
    exists_targetDefectVectors family L hLunit hLsource rho hrho
  let sigma := restrictedRepresentation L rho
  have heta_o_mem : eta_o ∈
      (⨅ n, (sigma (rootFlag n)).range) := by
    rw [Submodule.mem_iInf]
    intro n
    exact ⟨eta_o, heta_o_fixed n⟩
  let e (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : K ≃ₗᵢ[ℂ] K :=
    Unitary.linearIsometryEquiv
      (representedGeneratorUnitary L hLunit rho i)
  let eta (i : MathlibAnnex.CStarAlgebra.PureState.GNSClass Limit) : K := (e i).symm eta_o
  refine ⟨eta_o, eta, heta_o_norm, heta_o_fixed, heta_o_state, ?_⟩
  intro i
  have heta_norm : ‖eta i‖ = 1 := by
    rw [show ‖eta i‖ = ‖eta_o‖ by exact (e i).symm.norm_map eta_o]
    exact heta_o_norm
  obtain ⟨S, T, P, Q, R, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      htransport⟩ :=
    exists_targetShellReconstruction family L hLunit hLsource rho i
  have heta_mem : eta i ∈
      (⨅ n, (sigma (transportedFlag family i n)).range) := by
    apply (htransport (eta i)).2
    simpa [e, eta] using heta_o_mem
  have heta_fixed (n : ℕ) :
      sigma (transportedFlag family i n) (eta i) = eta i := by
    have hn : eta i ∈ (sigma (transportedFlag family i n)).range :=
      (Submodule.mem_iInf _).mp heta_mem n
    exact LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap
        (IsStarProjection.map_representation sigma
          (isStarProjection_transportedFlag family i n)).isIdempotentElem) |>.mp hn
  have heta_state : Representation.vectorFunctional sigma (eta i) =
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1 := by
    apply vectorFunctional_eq_of_compression_tendsto sigma
      (transportedFlag family i)
      (MathlibAnnex.CStarAlgebra.PureState.representative completedRootPureState i).1
      (fun n ↦ (isStarProjection_transportedFlag family i n).isSelfAdjoint.star_eq)
      (tendsto_representative_transported_compression family i)
      (eta i) heta_norm heta_fixed
  refine ⟨heta_norm, heta_fixed, ?_, heta_state⟩
  simp [e, eta]

end MathlibAnnex.CStarAlgebra.CAR
