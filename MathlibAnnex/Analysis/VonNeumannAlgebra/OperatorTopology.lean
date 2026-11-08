import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# Comparing the operator topologies

The strong operator topology is Mathlib's `PointwiseConvergenceCLM` topology;
the weak operator topology is carried by `ContinuousLinearMapWOT`.
This module connects these standard type copies with
`ContinuousLinearMap.StronglyConverges`.

Fixed precomposition and postcomposition are already continuous in both
topologies: use `PointwiseConvergenceCLM.precomp` and
`PointwiseConvergenceCLM.postcomp`, or the corresponding
`ContinuousLinearMapWOT.precompCLM` and `ContinuousLinearMapWOT.postcompCLM`.
The imported Hilbert-space WOT module also provides continuity of vector
functionals and the `ContinuousStar` instance.
-/

set_option autoImplicit false

open Filter Topology

namespace PointwiseConvergenceCLM

variable (𝕜 E F : Type*) [NormedField 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/-- The canonical continuous linear map from the strong operator topology to
the weak operator topology. -/
def toWOT : (E →Lₚₜ[𝕜] F) →L[𝕜] (E →WOT[𝕜] F) where
  toFun T := ContinuousLinearMapWOT.ofCLM T
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x φ ↦
    φ.continuous.comp (continuous_eval_const x)

/-- The comparison map does not change the underlying operator. -/
@[simp]
theorem toWOT_apply (T : E →Lₚₜ[𝕜] F) :
    toWOT 𝕜 E F T = ContinuousLinearMapWOT.ofCLM T :=
  rfl

end PointwiseConvergenceCLM

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

/-- Pointwise norm convergence is convergence in the standard strong operator
topology, with no restriction on the indexing filter. -/
theorem stronglyConverges_iff_tendsto_pointwiseConvergenceCLM
    {ι : Type*} {A : ι → E →L[𝕜] F} {l : Filter ι} {T : E →L[𝕜] F} :
    StronglyConverges A l T ↔
      Tendsto
        (fun i ↦ toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F (A i))
        l (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F T)) := by
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  rfl

/-- Operator-norm convergence implies strong convergence. -/
theorem stronglyConverges_of_tendsto
    {ι : Type*} {A : ι → E →L[𝕜] F} {l : Filter ι} {T : E →L[𝕜] F}
    (hA : Tendsto A l (𝓝 T)) :
    StronglyConverges A l T := by
  apply stronglyConverges_iff_tendsto_pointwiseConvergenceCLM.mpr
  exact (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E F).continuous.continuousAt.tendsto.comp hA

/-- A strongly convergent family converges in the standard weak operator
topology. -/
theorem StronglyConverges.tendsto_wot
    {ι : Type*} {A : ι → E →L[𝕜] F} {l : Filter ι} {T : E →L[𝕜] F}
    (hA : StronglyConverges A l T) :
    Tendsto (fun i ↦ ContinuousLinearMapWOT.ofCLM (A i)) l
      (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
  exact (PointwiseConvergenceCLM.toWOT 𝕜 E F).continuous.continuousAt.tendsto.comp
    (stronglyConverges_iff_tendsto_pointwiseConvergenceCLM.mp hA)

end ContinuousLinearMap
