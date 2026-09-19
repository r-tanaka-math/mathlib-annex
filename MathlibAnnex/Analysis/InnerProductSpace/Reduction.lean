import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator
import MathlibAnnex.Analysis.InnerProductSpace.OrthogonalSum

/-!
# Reduction and intertwining under strong limits

Closed invariant subspaces and bounded intertwiners pass to pointwise norm
limits.  Adjoint invariance is deliberately supplied through a second strong
limit rather than inferred from the first.
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProduct

namespace Submodule

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A subspace is invariant under a bounded operator. -/
def IsInvariantUnder (K : Submodule 𝕜 E) (T : E →L[𝕜] E) : Prop :=
  ∀ ⦃x⦄, x ∈ K → T x ∈ K

/-- A subspace reduces an operator when it is invariant under the operator and
its adjoint. -/
def Reduces (K : Submodule 𝕜 E) (T : E →L[𝕜] E) : Prop :=
  K.IsInvariantUnder T ∧ K.IsInvariantUnder (T†)

theorem IsInvariantUnder.strongLimit {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    {A : ι → E →L[𝕜] E} {T : E →L[𝕜] E}
    (hA : ContinuousLinearMap.StronglyConverges A l T)
    (hinv : ∀ i, K.IsInvariantUnder (A i)) : K.IsInvariantUnder T := by
  intro x hx
  exact hK.mem_of_tendsto (hA x) (Eventually.of_forall fun i ↦ hinv i hx)

theorem Reduces.strongLimits {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    {A : ι → E →L[𝕜] E} {B : ι → E →L[𝕜] E}
    {S T : E →L[𝕜] E}
    (hA : ContinuousLinearMap.StronglyConverges A l S)
    (hB : ContinuousLinearMap.StronglyConverges B l T)
    (hAdj : T = (S†))
    (hinvA : ∀ i, K.IsInvariantUnder (A i))
    (hinvB : ∀ i, K.IsInvariantUnder (B i)) : K.Reduces S := by
  refine ⟨IsInvariantUnder.strongLimit hK hA hinvA, ?_⟩
  simpa only [← hAdj] using IsInvariantUnder.strongLimit hK hB hinvB

/-- A closed subspace reducing every summand reduces a strong sum, provided
the adjoint partial sums are also known to converge strongly to the adjoint. -/
theorem Reduces.strongSum {K : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    {W : ℕ → E →L[𝕜] E} {S T : E →L[𝕜] E}
    (hW : ∀ n, K.Reduces (W n))
    (hS : ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum W) atTop S)
    (hT : ContinuousLinearMap.StronglyConverges
      (ContinuousLinearMap.partialSum fun n ↦ (W n)†) atTop T)
    (hAdj : T = S†) : K.Reduces S := by
  apply Reduces.strongLimits hK hS hT hAdj
  · intro N x hx
    rw [ContinuousLinearMap.partialSum_apply]
    exact K.sum_mem fun n _ ↦ (hW n).1 hx
  · intro N x hx
    rw [ContinuousLinearMap.partialSum_apply]
    exact K.sum_mem fun n _ ↦ (hW n).2 hx

end Submodule

namespace ContinuousLinearMap

variable {𝕜 E F G H : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace H]

/-- A bounded intertwining identity passes to two strong limits. -/
theorem intertwines_strongLimits {ι : Type*} {l : Filter ι} [l.NeBot]
    {A : ι → E →L[𝕜] F} {B : ι → G →L[𝕜] H}
    {S : E →L[𝕜] F} {T : G →L[𝕜] H}
    (L : F →L[𝕜] H) (R : E →L[𝕜] G)
    (hA : StronglyConverges A l S) (hB : StronglyConverges B l T)
    (hfinite : ∀ i, L.comp (A i) = (B i).comp R) :
    L.comp S = T.comp R := by
  apply ext
  intro x
  apply tendsto_nhds_unique (l := l)
  · exact (hA.comp_left L) x
  · simpa [hfinite] using (hB.comp_right R) x

end ContinuousLinearMap
