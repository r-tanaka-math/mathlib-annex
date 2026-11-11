/-
New typed consumers; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.MinimalColumnTransfer

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

universe u v w t

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

example (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (C : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra)
    (theta : M.toStarSubalgebra →⋆ₙₐ[ℂ] N.toStarSubalgebra)
    (U : H →ₗᵢ[ℂ] K)
    (hC : ∀ x : N.toStarSubalgebra, (C x : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint ∘L
        ((x : K →L[ℂ] K) ∘L U.toContinuousLinearMap))
    (hU : ∀ a : M.toStarSubalgebra,
      (theta a : K →L[ℂ] K) ∘L U.toContinuousLinearMap =
        U.toContinuousLinearMap ∘L (a : H →L[ℂ] H))
    (x : N.toStarSubalgebra) (a : M.toStarSubalgebra) :
    C (x * theta a) = C x * a := by
  exact VonNeumannAlgebra.compression_mul_lift M N C theta U hC hU x a

-- An arbitrary filter universe is consumed; the sequence bound is not an
-- additional assumption of the minimal-column norm identity.
example (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (C : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra)
    (theta : M.toStarSubalgebra →⋆ₙₐ[ℂ] N.toStarSubalgebra)
    (hCright : ∀ (x : N.toStarSubalgebra) (a : M.toStarSubalgebra),
      C (x * theta a) = C x * a)
    {e : N.toStarSubalgebra} (he : IsMinimalStarProjection e)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p)
    (hu : IsUnit (p * C e * p + (1 - p)))
    {ι : Type t} {l : Filter ι} (a : ι → M.toStarSubalgebra)
    (hap : ∀ i, a i * p = a i)
    (hs : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (theta (a i) : K →L[ℂ] K)) l 0) :
    Tendsto a l (𝓝 0) := by
  exact M.tendsto_zero_of_minimal_column_bimodule N C theta hCright he hp hu a hap hs

example (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (hM : M.IsTypeII1) (hN : N.IsFactor)
    (C : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra)
    (theta : M.toStarSubalgebra →⋆ₙₐ[ℂ] N.toStarSubalgebra)
    (U : H →ₗᵢ[ℂ] K) {ξ : H} (hξ : ξ ≠ 0)
    (hC : ∀ x : N.toStarSubalgebra, (C x : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint ∘L
        ((x : K →L[ℂ] K) ∘L U.toContinuousLinearMap))
    (hU : ∀ a : M.toStarSubalgebra,
      (theta a : K →L[ℂ] K) ∘L U.toContinuousLinearMap =
        U.toContinuousLinearMap ∘L (a : H →L[ℂ] H))
    (hs : ∀ a : ℕ → M.toStarSubalgebra, (∀ n, ‖a n‖ ≤ 1) →
      ContinuousLinearMap.StronglyConverges (fun n ↦ (a n : H →L[ℂ] H)) atTop 0 →
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (theta (a n) : K →L[ℂ] K)) atTop 0) :
    ¬ N.IsTypeI := by
  exact M.not_isTypeI_of_isTypeII1_compression_lift N hM hN C theta U hξ hC hU hs

-- The application consumes the actual all-state-envelope lift. No inverse
-- map, normality predicate, or extra strong continuity input appears here.
example {A : Type w} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsNondegenerate)
    (sigma : NonUnitalCStarRepresentation A H) (hsigma : sigma.IsNondegenerate)
    (N : VonNeumannAlgebra K)
    (hLN : VonNeumannAlgebra.generated rho.unitization.range ≤ N)
    (hM : (VonNeumannAlgebra.generated sigma.unitization.range).IsTypeII1)
    (hN : N.IsFactor)
    (C : N.toStarSubalgebra →P[ℂ]
      (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (U : H →ₗᵢ[ℂ] K) {ξ : H} (hξ : ξ ≠ 0)
    (hC : ∀ x : N.toStarSubalgebra, (C x : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint ∘L
        ((x : K →L[ℂ] K) ∘L U.toContinuousLinearMap))
    (hU : ∀ a : A, (rho a).comp U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp (sigma a)) :
    ¬ N.IsTypeI := by
  exact Representation.not_isTypeI_of_isTypeII1_generated_compression
    rho hrho sigma hsigma N hLN hM hN C U hξ hC hU
