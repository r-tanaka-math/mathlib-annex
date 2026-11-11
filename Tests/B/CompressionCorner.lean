import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CompressionCorner

/-!
# Typed consumers for the concrete intertwining compression corner

These examples use the constructed section and the supplied operator
carriers. They neither postulate a section nor assume its strong continuity.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra InnerProduct
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v w t

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsNondegenerate)
variable (sigma : NonUnitalCStarRepresentation A H) (hsigma : sigma.IsNondegenerate)
variable (U : H →ₗᵢ[ℂ] K)
variable (hU : ∀ a : A, (rho a).comp U.toContinuousLinearMap =
  U.toContinuousLinearMap.comp (sigma a))

-- The lift is a genuine star homomorphism into the original large algebra.
include hrho hsigma in
example :
    (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra →⋆ₙₐ[ℂ]
      (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra :=
  compressionLift rho hrho sigma hsigma

-- Its support need not be the ambient unit.
example : compressionLift rho hrho sigma hsigma 1 =
    compressionSupport rho hrho sigma hsigma :=
  compressionLift_one rho hrho sigma hsigma

example : IsStarProjection (compressionSupport rho hrho sigma hsigma) :=
  isStarProjection_compressionSupport rho hrho sigma hsigma

example (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
    compressionSupport rho hrho sigma hsigma * T =
      T * compressionSupport rho hrho sigma hsigma :=
  compressionSupport_commute rho hrho sigma hsigma T

include hrho hsigma U hU

example (S : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
    (envelopingRepresentationExtension rho hrho S : K →L[ℂ] K).comp
        U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp
        (envelopingRepresentationExtension sigma hsigma S : H →L[ℂ] H) :=
  envelopingRepresentationExtension_intertwines rho hrho sigma hsigma U hU S

example (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    (compressionLift rho hrho sigma hsigma a : K →L[ℂ] K).comp U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp (a : H →L[ℂ] H) :=
  compressionLift_intertwines rho hrho sigma hsigma U hU a

example (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        ((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K).comp
          U.toContinuousLinearMap) = (a : H →L[ℂ] H) :=
  compression_compressionLift rho hrho sigma hsigma U hU a

example : Function.Injective (compressionLift rho hrho sigma hsigma) :=
  injective_compressionLift rho hrho sigma hsigma U hU

example (a : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra) :
    ‖compressionLift rho hrho sigma hsigma a‖ = ‖a‖ :=
  norm_compressionLift rho hrho sigma hsigma U hU a

example : Isometry (compressionLift rho hrho sigma hsigma) :=
  isometry_compressionLift rho hrho sigma hsigma U hU

-- The middle operator ranges over all B(K); no generated-algebra premise occurs.
example
    (a b : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (T : K →L[ℂ] K) :
    U.toContinuousLinearMap.adjoint.comp
        (((compressionLift rho hrho sigma hsigma a : K →L[ℂ] K) * T *
          (compressionLift rho hrho sigma hsigma b : K →L[ℂ] K)).comp
            U.toContinuousLinearMap) =
      (a : H →L[ℂ] H) *
        (U.toContinuousLinearMap.adjoint.comp (T.comp U.toContinuousLinearMap)) *
        (b : H →L[ℂ] H) :=
  compressionLift_mul_mul rho hrho sigma hsigma U hU a b T

example (T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
    U.toContinuousLinearMap.adjoint.comp
        ((T : K →L[ℂ] K).comp U.toContinuousLinearMap) = 0 ↔
      compressionSupport rho hrho sigma hsigma * T = 0 :=
  compression_eq_zero_iff_compressionSupport_mul_eq_zero rho hrho sigma hsigma U hU T

example :
    U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint ∈
      (VonNeumannAlgebra.generated rho.unitization.range).commutant :=
  rangeProjection_mem_commutant rho hrho sigma hsigma U hU

example :
    (compressionSupport rho hrho sigma hsigma : K →L[ℂ] K) =
      (VonNeumannAlgebra.centralSupport
        (VonNeumannAlgebra.generated rho.unitization.range).commutant
        ⟨U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint,
          rangeProjection_mem_commutant rho hrho sigma hsigma U hU⟩ : K →L[ℂ] K) :=
  compressionSupport_eq_centralSupport rho hrho sigma hsigma U hU

omit hrho hsigma U hU

example : Set.range (compressionLift rho hrho sigma hsigma) =
    {T | compressionSupport rho hrho sigma hsigma * T = T} :=
  range_compressionLift rho hrho sigma hsigma

include hrho hsigma U hU

-- This is an equivalence with the supplied concrete corner, not a new carrier.
example :
    (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra ≃⋆ₐ[ℂ]
      VonNeumannAlgebra.corner (VonNeumannAlgebra.generated rho.unitization.range)
        (compressionSupport rho hrho sigma hsigma)
        (isStarProjection_compressionSupport rho hrho sigma hsigma) :=
  compressionCornerEquiv rho hrho sigma hsigma U hU

example
    (T : VonNeumannAlgebra.corner (VonNeumannAlgebra.generated rho.unitization.range)
      (compressionSupport rho hrho sigma hsigma)
      (isStarProjection_compressionSupport rho hrho sigma hsigma)) :
    ((compressionCornerEquiv rho hrho sigma hsigma U hU).symm T : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint.comp
        (((T : (VonNeumannAlgebra.generated rho.unitization.range).toStarSubalgebra) :
          K →L[ℂ] K).comp U.toContinuousLinearMap) :=
  compressionCornerEquiv_symm_apply_coe rho hrho sigma hsigma U hU T

-- Arbitrary filters are permitted; zero/empty Hilbert components stay meaningful.
example {ι : Type t} (l : Filter ι)
    (a : ι → (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (ha : ContinuousLinearMap.StronglyConverges (fun i => (a i : H →L[ℂ] H)) l 0)
    (r : ℝ) (hr : ∀ i, ‖a i‖ ≤ r) :
    ContinuousLinearMap.StronglyConverges
      (fun i => (compressionLift rho hrho sigma hsigma (a i) : K →L[ℂ] K)) l 0 :=
  stronglyConverges_compressionLift_zero rho hrho sigma hsigma U hU l a ha r hr

example {ι : Type t} (l : Filter ι)
    (a : ι → (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (a0 : (VonNeumannAlgebra.generated sigma.unitization.range).toStarSubalgebra)
    (ha : ContinuousLinearMap.StronglyConverges (fun i => (a i : H →L[ℂ] H)) l
      (a0 : H →L[ℂ] H)) (r : ℝ) (hr : ∀ i, ‖a i‖ ≤ r) :
    ContinuousLinearMap.StronglyConverges
      (fun i => (compressionLift rho hrho sigma hsigma (a i) : K →L[ℂ] K)) l
      (compressionLift rho hrho sigma hsigma a0 : K →L[ℂ] K) :=
  stronglyConverges_compressionLift rho hrho sigma hsigma U hU l a a0 ha r hr

omit hrho hsigma U hU

-- Closed orbit membership is consumed with the already supplied central support.
example (L : VonNeumannAlgebra K) (p : L.toStarSubalgebra)
    (V : Submodule ℂ K) (hV : IsClosed (V : Set K))
    (horbit : ∀ (b : L.toStarSubalgebra) (x : K),
      (b : K →L[ℂ] K) ((p : K →L[ℂ] K) x) ∈ V) (x : K) :
    (VonNeumannAlgebra.centralSupport L p : K →L[ℂ] K) x ∈ V :=
  VonNeumannAlgebra.centralSupport_apply_mem_of_forall_mul_apply_mem L p V hV horbit x

