import MathlibAnnex.Analysis.VonNeumannAlgebra.FiniteAmplification
import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# The bicommutant theorem

For a unital star subalgebra of bounded operators on an arbitrary complex
Hilbert space, its bicommutant is both its strong and its weak operator
closure. The closures below are taken on Mathlib's standard topology copies.

The finite-amplification argument supplies simultaneous approximation on
every finite family of vectors. The pointwise-convergence neighborhood basis
turns this into strong closure membership. Continuity of the comparison map
then gives weak closure membership, and the weak closedness of commutants
gives the converse inclusion.
-/

set_option autoImplicit false

open Set Filter Topology

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem mem_sot_closure_of_mem_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ generated S) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H))) := by
  classical
  have hb := PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
    (σ := RingHom.id ℂ) (E := H) (F := H)
    (Metric.nhds_basis_ball (x := (0 : H)))
  apply (mem_closure_iff_nhds_basis
    (hb.nhds_of_zero
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T))).2
  rintro ⟨F, ε⟩ ⟨hF, hε⟩
  letI : Fintype F := @Fintype.ofFinite F hF
  obtain ⟨A, hAS, hA⟩ :=
    S.exists_forall_apply_sub_norm_lt_of_mem_bicommutant
      ((mem_generated_iff S T).mp hT) (fun x : F ↦ (x : H)) hε
  refine ⟨ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H A,
    ⟨A, hAS, rfl⟩, ?_⟩
  intro x hx
  change A x - T x ∈ Metric.ball (0 : H) ε
  simpa only [Metric.mem_ball, dist_zero_right] using hA ⟨x, hx⟩

private theorem mem_wot_closure_of_mem_sot_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H)))) :
    ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H))) := by
  have h := mem_closure_image
    (PointwiseConvergenceCLM.toWOT ℂ H H).continuous.continuousAt hT
  have hcomp : (fun U : H →L[ℂ] H ↦ PointwiseConvergenceCLM.toWOT ℂ H H
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H U)) =
      ContinuousLinearMapWOT.ofCLM := rfl
  have hT' := congrFun hcomp T
  rw [Set.image_image, hcomp] at h
  exact hT' ▸ h

private theorem mem_generated_of_mem_wot_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : ContinuousLinearMapWOT.ofCLM T ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)))) :
    T ∈ generated S := by
  have hsubset : ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)) ⊆
      ContinuousLinearMapWOT.ofCLM '' (generated S : Set (H →L[ℂ] H)) :=
    Set.image_mono (subset_generated S)
  have hmem := closure_minimal hsubset (isClosed_wot (generated S)) hT
  obtain ⟨A, hA, hAT⟩ := hmem
  have hAT' : A = T := ContinuousLinearMapWOT.ofCLM_injective hAT
  exact hAT' ▸ hA

/-- The bicommutant of a unital star subalgebra is its closure in the standard
strong operator topology. No irreducibility, separability, dimension, or
nonzero-space assumption is required. -/
theorem mem_generated_iff_mem_sotClosure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ generated S ↔
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
        closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          (S : Set (H →L[ℂ] H))) :=
  ⟨mem_sot_closure_of_mem_generated S,
    fun h ↦ mem_generated_of_mem_wot_closure S (mem_wot_closure_of_mem_sot_closure S h)⟩

/-- The bicommutant of a unital star subalgebra is its closure in the standard
weak operator topology. -/
theorem mem_generated_iff_mem_wotClosure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    T ∈ generated S ↔
      ContinuousLinearMapWOT.ofCLM T ∈
        closure (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H))) :=
  ⟨fun h ↦ mem_wot_closure_of_mem_sot_closure S (mem_sot_closure_of_mem_generated S h),
    mem_generated_of_mem_wot_closure S⟩

end VonNeumannAlgebra
