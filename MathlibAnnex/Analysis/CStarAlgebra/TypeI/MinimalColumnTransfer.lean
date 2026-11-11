/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The proof implements the minimal-column route supplied in the dispatch.
The minimal projection, quantitative inverse, strongly null projections and
compression lift are proved in their respective new modules.  No implication
from merely containing a II₁ subalgebra is asserted.
-/

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.MinimalColumn
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.SpectralCutoff
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalSequence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CompressionCorner
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NormalCompression

/-!
# Non-type-I transfer through an actual compression

A type I source factor supplies a minimal projection detected by the
compression.  A quantitative cutoff of its positive image turns strong
convergence in the test corner into norm convergence through the minimal
column.  An actual II₁ corner has a strongly null norm-one projection sequence,
giving the contradiction.

The first lemmas expose their algebraic hypotheses.  The compression-corner
construction is consumed below to discharge the lift hypotheses in the
representation application.  None is an extra hypothesis of a claimed final
Glimm--Sakai equivalence.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

universe u v w

namespace VonNeumannAlgebra

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The right bimodule identity follows from the actual compression formula
and the actual intertwiner, on every element of the source von Neumann algebra. -/
theorem compression_mul_lift
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
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
  apply Subtype.ext
  ext ξ
  change (C (x * theta a) : H →L[ℂ] H) ξ = (C x : H →L[ℂ] H) ((a : H →L[ℂ] H) ξ)
  rw [hC, hC]
  change U.toContinuousLinearMap.adjoint
      ((x : K →L[ℂ] K) ((theta a : K →L[ℂ] K) (U ξ))) =
    U.toContinuousLinearMap.adjoint ((x : K →L[ℂ] K) (U ((a : H →L[ℂ] H) ξ)))
  exact congrArg (fun η : K ↦ U.toContinuousLinearMap.adjoint ((x : K →L[ℂ] K) η))
    (congrArg (fun T : H →L[ℂ] K ↦ T ξ) (hU a))

/-- A minimal-domain column and an actual inverse on the test corner turn
a lifted strongly null net into a norm-null net.  Only right bimodularity
and norm continuity of the positive map are used in this lemma. -/
theorem tendsto_zero_of_minimal_column_bimodule
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (C : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra)
    (theta : M.toStarSubalgebra →⋆ₙₐ[ℂ] N.toStarSubalgebra)
    (hCright : ∀ (x : N.toStarSubalgebra) (a : M.toStarSubalgebra),
      C (x * theta a) = C x * a)
    {e : N.toStarSubalgebra} (he : IsMinimalStarProjection e)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p)
    (hu : IsUnit (p * C e * p + (1 - p)))
    {ι : Type w} {l : Filter ι} (a : ι → M.toStarSubalgebra)
    (hap : ∀ i, a i * p = a i)
    (hstrong : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (theta (a i) : K →L[ℂ] K)) l 0) :
    Tendsto a l (𝓝 0) := by
  let y : ι → N.toStarSubalgebra := fun i ↦ theta (a i) * e
  have hy (i : ι) : y i * e = y i := by
    dsimp only [y]
    rw [mul_assoc, he.isStarProjection.isIdempotentElem.eq]
  have hys : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (y i : K →L[ℂ] K)) l 0 := by
    intro ξ
    change Tendsto (fun i ↦ (theta (a i) : K →L[ℂ] K) ((e : K →L[ℂ] K) ξ))
      l (𝓝 0)
    simpa only [ContinuousLinearMap.zero_apply] using hstrong ((e : K →L[ℂ] K) ξ)
  have hyn := N.tendsto_zero_of_stronglyConverges_minimal_column he y hy hys
  have hyn' : Tendsto y l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    change Tendsto (fun i ↦ ‖(y i : K →L[ℂ] K)‖) l (𝓝 0)
    simpa only [norm_zero] using hyn.norm
  have hystar : Tendsto (fun i ↦ star (y i)) l (𝓝 0) := by
    simpa only [star_zero] using hyn'.star
  have hCy : Tendsto (fun i ↦ C (star (y i))) l (𝓝 0) := by
    change Tendsto (C.toContinuousLinearMap ∘ fun i ↦ star (y i)) l (𝓝 0)
    simpa only [map_zero] using
      C.toContinuousLinearMap.continuous.continuousAt.tendsto.comp hystar
  have hidentity (i : ι) :
      (Ring.inverse (p * C e * p + (1 - p)) * p) * C (star (y i)) = star (a i) := by
    have hstar : star (y i) = e * theta (star (a i)) := by
      simp only [y, star_mul, he.isStarProjection.isSelfAdjoint.star_eq, map_star]
    have hpa : p * star (a i) = star (a i) := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star (hap i)
    rw [hstar, hCright]
    simpa only [mul_assoc] using
      M.ringInverse_sandwich_add_one_sub_mul_of_mul_eq_right hp hu hpa
  have hlim : Tendsto (fun i ↦
      (Ring.inverse (p * C e * p + (1 - p)) * p) * C (star (y i))) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hCy
  have hstar : Tendsto (fun i ↦ star (a i)) l (𝓝 0) :=
    hlim.congr' (Eventually.of_forall hidentity)
  simpa only [star_star, star_zero] using hstar.star

/-- An actual compression with an intertwining lift continuous on strongly
null bounded sequences cannot have a type I factor as source and an II₁
algebra as target.  The lift is a concrete star homomorphism, not a class
containing the desired conclusion. -/
theorem not_isTypeI_of_isTypeII1_compression_lift
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
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
    (hstrong : ∀ a : ℕ → M.toStarSubalgebra, (∀ n, ‖a n‖ ≤ 1) →
      ContinuousLinearMap.StronglyConverges (fun n ↦ (a n : H →L[ℂ] H)) atTop 0 →
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (theta (a n) : K →L[ℂ] K)) atTop 0) :
    ¬ N.IsTypeI := by
  intro hI
  obtain ⟨e, he, heC⟩ :=
    hN.exists_minimal_projection_compression_ne_zero_of_isometry hI U hξ
  have hCe : C e ≠ 0 := by
    intro hzero
    apply heC
    have hz : (C e : H →L[ℂ] H) = 0 := congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) hzero
    simpa only [ContinuousLinearMap.comp_assoc] using (hC e).symm.trans hz
  obtain ⟨ε, p, hε, hp, hp0, _, hle⟩ :=
    M.exists_nonzero_projection_smul_le (C e) (C.map_nonneg he.isStarProjection.nonneg) hCe
  have hu := M.isUnit_sandwich_add_one_sub hp hε hle
  obtain ⟨q, hq, _, hqstrong⟩ :=
    hM.exists_stronglyConverges_zero_projection_sequence hp hp0
  have hqnorm : ∀ n, ‖q n‖ ≤ 1 := fun n ↦ (hq n).2.2.le
  have hqp (n : ℕ) : q n * p = q n :=
    ((hq n).1.le_iff_mul_eq_left hp).mp (hq n).2.1
  have hnorm := M.tendsto_zero_of_minimal_column_bimodule N C theta
    (compression_mul_lift M N C theta U hC hU) he hp hu q hqp
    (hstrong q hqnorm hqstrong)
  have hnorm0 : Tendsto (fun n ↦ ‖q n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hnorm.norm
  have hnorm1 : Tendsto (fun n ↦ ‖q n‖) atTop (𝓝 (1 : ℝ)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).congr'
      (Eventually.of_forall fun n ↦ (hq n).2.2.symm)
  exact zero_ne_one (tendsto_nhds_unique hnorm0 hnorm1)

end VonNeumannAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

variable {A : Type w} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Non-type-I transfer for the actual common-source representations.
The central corner lift, its intertwining identity and its bounded strong
continuity are constructed from the all-state envelope inside the proof.
Only the displayed compression, not an abstract normality predicate or
an assumed inverse map, is supplied by the representation application. -/
theorem not_isTypeI_of_isTypeII1_generated_compression
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
  let M := VonNeumannAlgebra.generated sigma.unitization.range
  let L := VonNeumannAlgebra.generated rho.unitization.range
  let incl : L.toStarSubalgebra →⋆ₐ[ℂ] N.toStarSubalgebra :=
    StarSubalgebra.inclusion hLN
  let theta : M.toStarSubalgebra →⋆ₙₐ[ℂ] N.toStarSubalgebra :=
    incl.toNonUnitalStarAlgHom.comp (compressionLift rho hrho sigma hsigma)
  apply VonNeumannAlgebra.not_isTypeI_of_isTypeII1_compression_lift
    M N hM hN C theta U hξ hC
  · intro a
    change (compressionLift rho hrho sigma hsigma a : K →L[ℂ] K).comp
        U.toContinuousLinearMap =
      U.toContinuousLinearMap.comp (a : H →L[ℂ] H)
    exact compressionLift_intertwines rho hrho sigma hsigma U hU a
  · intro a ha hstrong
    change ContinuousLinearMap.StronglyConverges
      (fun n ↦ (compressionLift rho hrho sigma hsigma (a n) : K →L[ℂ] K)) atTop 0
    exact stronglyConverges_compressionLift_zero rho hrho sigma hsigma U hU
      atTop a hstrong 1 ha

end MathlibAnnex.Analysis.CStarAlgebra.Representation
