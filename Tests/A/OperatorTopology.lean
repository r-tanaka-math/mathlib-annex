import MathlibAnnex.Analysis.VonNeumannAlgebra.OperatorTopology

/-!
# Typed consumers for the operator topologies

All statements use the standard SOT/WOT type copies.  The filters, Hilbert
spaces, and fixed multipliers are unrestricted.
-/

set_option autoImplicit false

open Filter Topology

namespace OperatorTopologyExamples

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_tendsto_sot {ι : Type*} {l : Filter ι}
    {A : ι → H →L[ℂ] H} {T : H →L[ℂ] H} (h : Tendsto A l (𝓝 T)) :
    Tendsto
      (fun i ↦ ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (A i))
      l (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T)) :=
  ContinuousLinearMap.stronglyConverges_iff_tendsto_pointwiseConvergenceCLM.mp
    (ContinuousLinearMap.stronglyConverges_of_tendsto h)

theorem strong_tendsto_wot {ι : Type*} {l : Filter ι}
    {A : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (h : ContinuousLinearMap.StronglyConverges A l T) :
    Tendsto (fun i ↦ ContinuousLinearMapWOT.ofCLM (A i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
  h.tendsto_wot

theorem continuous_sot_to_wot :
    Continuous (fun T : H →Lₚₜ[ℂ] H ↦ ContinuousLinearMapWOT.ofCLM T) :=
  (PointwiseConvergenceCLM.toWOT ℂ H H).continuous

theorem continuous_sot_left (Q : H →L[ℂ] H) :
    Continuous (fun T : H →Lₚₜ[ℂ] H ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (Q.comp T)) :=
  (PointwiseConvergenceCLM.postcomp H Q).continuous

theorem continuous_sot_right (Q : H →L[ℂ] H) :
    Continuous (fun T : H →Lₚₜ[ℂ] H ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (T.comp Q)) :=
  (PointwiseConvergenceCLM.precomp H Q).continuous

theorem continuous_wot_left (Q : H →L[ℂ] H) :
    Continuous (fun T : H →WOT[ℂ] H ↦ ContinuousLinearMapWOT.ofCLM Q * T) := by
  change Continuous (fun T : H →WOT[ℂ] H ↦ (ContinuousLinearMapWOT.ofCLM Q).comp T)
  exact ContinuousLinearMapWOT.continuous_postcomp _

theorem continuous_wot_right (Q : H →L[ℂ] H) :
    Continuous (fun T : H →WOT[ℂ] H ↦ T * ContinuousLinearMapWOT.ofCLM Q) := by
  change Continuous (fun T : H →WOT[ℂ] H ↦ T.comp (ContinuousLinearMapWOT.ofCLM Q))
  exact ContinuousLinearMapWOT.continuous_precomp _

theorem continuous_wot_matrix_coefficient (x y : H) :
    Continuous (fun T : H →WOT[ℂ] H ↦ inner ℂ y (T x)) :=
  ContinuousLinearMapWOT.continuous_inner_apply continuous_id x y

theorem continuous_wot_adjoint :
    Continuous (star : (H →WOT[ℂ] H) → (H →WOT[ℂ] H)) :=
  continuous_star

theorem strong_multiplication_by_fixed {ι : Type*} {l : Filter ι}
    {A : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (h : ContinuousLinearMap.StronglyConverges A l T) (Q : H →L[ℂ] H) :
    ContinuousLinearMap.StronglyConverges (fun i ↦ Q * A i) l (Q * T) ∧
      ContinuousLinearMap.StronglyConverges (fun i ↦ A i * Q) l (T * Q) :=
  ⟨h.comp_left Q, h.comp_right Q⟩

end OperatorTopologyExamples
