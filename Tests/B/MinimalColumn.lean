/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Typed consumers of the production results.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.MinimalColumn

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

universe u v w

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

example (M : VonNeumannAlgebra K) (e : M.toStarSubalgebra)
    (he : IsMinimalStarProjection e) :
    ∃ η : K, (e : K →L[ℂ] K) η = η ∧ ‖η‖ = 1 :=
  M.exists_unit_fixed_vector_of_minimal_projection he

example (M : VonNeumannAlgebra K) (e y : M.toStarSubalgebra)
    (he : IsMinimalStarProjection e) (η : K)
    (heη : (e : K →L[ℂ] K) η = η) (hη : ‖η‖ = 1)
    (hy : y * e = y) : ‖(y : K →L[ℂ] K)‖ = ‖(y : K →L[ℂ] K) η‖ :=
  M.norm_eq_apply_of_mem_minimal_column he heη hη hy

example (M : VonNeumannAlgebra K) (e y : M.toStarSubalgebra)
    (he : IsMinimalStarProjection e) (η : K)
    (heη : (e : K →L[ℂ] K) η = η) (hη : ‖η‖ = 1)
    (hy : y * e = y) (hzero : (y : K →L[ℂ] K) η = 0) : y = 0 := by
  apply Subtype.ext
  apply norm_eq_zero.mp
  rw [M.norm_eq_apply_of_mem_minimal_column he heη hη hy, hzero, norm_zero]

example (M : VonNeumannAlgebra K) (e : M.toStarSubalgebra)
    (he : IsMinimalStarProjection e) {ι : Type w} {l : Filter ι}
    (y : ι → M.toStarSubalgebra) (hy : ∀ i, y i * e = y i)
    (hstrong : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (y i : K →L[ℂ] K)) l 0) :
    Tendsto (fun i ↦ (y i : K →L[ℂ] K)) l (𝓝 0) :=
  M.tendsto_zero_of_stronglyConverges_minimal_column he y hy hstrong

example (M : VonNeumannAlgebra K) (e z : M.toStarSubalgebra)
    (he : IsMinimalStarProjection e) {ι : Type w} {l : Filter ι}
    (y : ι → M.toStarSubalgebra) (hy : ∀ i, y i * e = y i) (hz : z * e = z)
    (hstrong : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (y i : K →L[ℂ] K)) l (z : K →L[ℂ] K)) :
    Tendsto (fun i ↦ (y i : K →L[ℂ] K)) l (𝓝 (z : K →L[ℂ] K)) :=
  M.tendsto_of_stronglyConverges_minimal_column he y hy hz hstrong

example (M : VonNeumannAlgebra K) {ι : Type w}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    (hsup : M.iSupProjection p hp = 1) (U : H →L[ℂ] K) (hU : U ≠ 0) :
    ∃ i, U.adjoint ∘L (p i : K →L[ℂ] K) ∘L U ≠ 0 :=
  M.exists_projection_compression_ne_zero_of_iSupProjection_eq_one p hp hsup U hU

example (M : VonNeumannAlgebra K) (hM : M.IsFactor) (hI : M.IsTypeI)
    (U : H →L[ℂ] K) (hU : U ≠ 0) :
    ∃ e : M.toStarSubalgebra, IsMinimalStarProjection e ∧
      U.adjoint ∘L (e : K →L[ℂ] K) ∘L U ≠ 0 :=
  hM.exists_minimal_projection_compression_ne_zero hI U hU

example (M : VonNeumannAlgebra K) (hM : M.IsFactor) (hI : M.IsTypeI)
    (U : H →ₗᵢ[ℂ] K) (ξ : H) (hξ : ξ ≠ 0) :
    ∃ e : M.toStarSubalgebra, IsMinimalStarProjection e ∧
      U.toContinuousLinearMap.adjoint ∘L (e : K →L[ℂ] K) ∘L
        U.toContinuousLinearMap ≠ 0 :=
  hM.exists_minimal_projection_compression_ne_zero_of_isometry hI U hξ
