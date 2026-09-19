import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Strong convergence of continuous linear maps

Small pointwise-convergence lemmas for bounded operators.  The topology is
kept explicit: this file does not identify strong convergence with operator
norm convergence, and statements involving adjoints require a separate
convergence hypothesis for the adjoint family.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- Pointwise norm convergence of a family of bounded linear operators. -/
def StronglyConverges {ι : Type*} (A : ι → E →L[𝕜] F) (l : Filter ι)
    (T : E →L[𝕜] F) : Prop :=
  ∀ x, Tendsto (fun i ↦ A i x) l (𝓝 (T x))

theorem stronglyConverges_iff_tendsto_apply {ι : Type*} {A : ι → E →L[𝕜] F}
    {l : Filter ι} {T : E →L[𝕜] F} :
    StronglyConverges A l T ↔ ∀ x, Tendsto (fun i ↦ A i x) l (𝓝 (T x)) :=
  Iff.rfl

theorem StronglyConverges.const {ι : Type*} {l : Filter ι} (A : E →L[𝕜] F) :
    StronglyConverges (fun _ : ι ↦ A) l A :=
  fun _ ↦ tendsto_const_nhds

theorem StronglyConverges.add {ι : Type*} {A B : ι → E →L[𝕜] F} {l : Filter ι}
    {S T : E →L[𝕜] F} (hA : StronglyConverges A l S)
    (hB : StronglyConverges B l T) :
    StronglyConverges (fun i ↦ A i + B i) l (S + T) := by
  intro x
  simpa using (hA x).add (hB x)

theorem StronglyConverges.sub {ι : Type*} {A B : ι → E →L[𝕜] F} {l : Filter ι}
    {S T : E →L[𝕜] F} (hA : StronglyConverges A l S)
    (hB : StronglyConverges B l T) :
    StronglyConverges (fun i ↦ A i - B i) l (S - T) := by
  intro x
  simpa using (hA x).sub (hB x)

theorem StronglyConverges.comp_left {ι : Type*} {A : ι → E →L[𝕜] F}
    {l : Filter ι} {S : E →L[𝕜] F} (hA : StronglyConverges A l S)
    (C : F →L[𝕜] G) :
    StronglyConverges (fun i ↦ C.comp (A i)) l (C.comp S) := by
  intro x
  change Tendsto (fun i ↦ C (A i x)) l (𝓝 (C (S x)))
  convert C.continuous.continuousAt.tendsto.comp (hA x) using 1
  rfl

theorem StronglyConverges.comp_right {ι : Type*} {A : ι → F →L[𝕜] G}
    {l : Filter ι} {S : F →L[𝕜] G} (hA : StronglyConverges A l S)
    (C : E →L[𝕜] F) :
    StronglyConverges (fun i ↦ (A i).comp C) l (S.comp C) := by
  intro x
  exact hA (C x)

/-- Products of strongly convergent operator families converge strongly when
the left factors have a uniform operator-norm bound. -/
theorem StronglyConverges.comp_of_uniformlyBounded {ι : Type*} {l : Filter ι}
    {A : ι → F →L[𝕜] G} {B : ι → E →L[𝕜] F}
    {S : F →L[𝕜] G} {T : E →L[𝕜] F}
    (hA : StronglyConverges A l S) (hB : StronglyConverges B l T)
    (C : ℝ) (hC : ∀ i, ‖A i‖ ≤ C) :
    StronglyConverges (fun i ↦ (A i).comp (B i)) l (S.comp T) := by
  intro x
  have hzero : Tendsto (fun i ↦ A i (B i x - T x)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · filter_upwards [] with i
      exact norm_nonneg _
    · filter_upwards [] with i
      exact (A i).le_of_opNorm_le (hC i) _
    · have hsub : Tendsto (fun i ↦ B i x - T x) l (𝓝 0) := by
        simpa using (hB x).sub_const (T x)
      simpa using (tendsto_const_nhds.mul hsub.norm)
  have hfixed : Tendsto (fun i ↦ A i (T x)) l (𝓝 (S (T x))) := hA (T x)
  have hadd := hzero.add hfixed
  simpa [ContinuousLinearMap.comp_apply, map_sub, sub_add_cancel] using hadd

/-- If operators and their adjoints converge strongly and every finite pair
satisfies the adjoint identity, the two strong limits remain adjoint. -/
theorem adjoint_eq_of_stronglyConverges {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → E →L[𝕜] F} {B : ι → F →L[𝕜] E}
    {S : E →L[𝕜] F} {T : F →L[𝕜] E}
    (hA : StronglyConverges A l S) (hB : StronglyConverges B l T)
    (hAdj : ∀ i, B i = (A i)†) : T = S† := by
  apply (eq_adjoint_iff T S).2
  intro y x
  apply tendsto_nhds_unique (l := l)
  · exact (hB y).inner tendsto_const_nhds
  · simpa [hAdj, adjoint_inner_left] using
      (tendsto_const_nhds.inner (hA x))

end ContinuousLinearMap
