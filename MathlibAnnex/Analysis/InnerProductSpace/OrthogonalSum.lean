import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathlibAnnex.Analysis.InnerProductSpace.DecreasingProjection

/-!
# Strong sums of orthogonal operator families

This file constructs the two pointwise sums of an operator family and its
adjoint family independently.  The product identities are then recovered from
finite identities by a uniformly-bounded strong-product argument.
-/

set_option autoImplicit false

open Filter Topology
open scoped Function InnerProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The prefix sum with indices `0, ..., N - 1`. -/
def partialSum (W : ℕ → E →L[𝕜] F) (N : ℕ) : E →L[𝕜] F :=
  ∑ n ∈ Finset.range N, W n

@[simp]
theorem partialSum_apply (W : ℕ → E →L[𝕜] F) (N : ℕ) (x : E) :
    partialSum W N x = ∑ n ∈ Finset.range N, W n x := by
  simp [partialSum]

/-- Initial spaces of distinct terms are orthogonal.  With the convention that
`W† W` is the initial projection, this is the cross-product identity
`W_m W_n† = 0`. -/
def PairwiseInitialOrthogonal (W : ℕ → E →L[𝕜] F) : Prop :=
  ∀ ⦃m n⦄, m ≠ n → (W m).comp ((W n)†) = 0

/-- Final (range) spaces of distinct terms are orthogonal.  With the convention
that `W W†` is the final projection, this is the cross-product identity
`W_m† W_n = 0`. -/
def PairwiseFinalOrthogonal (W : ℕ → E →L[𝕜] F) : Prop :=
  ∀ ⦃m n⦄, m ≠ n → ((W m)†).comp (W n) = 0

theorem pairwiseInitialOrthogonal_adjoint_iff (W : ℕ → E →L[𝕜] F) :
    PairwiseInitialOrthogonal (fun n ↦ (W n)†) ↔ PairwiseFinalOrthogonal W := by
  simp only [PairwiseInitialOrthogonal, PairwiseFinalOrthogonal, adjoint_adjoint]

theorem pairwiseFinalOrthogonal_adjoint_iff (W : ℕ → E →L[𝕜] F) :
    PairwiseFinalOrthogonal (fun n ↦ (W n)†) ↔ PairwiseInitialOrthogonal W := by
  simp only [PairwiseInitialOrthogonal, PairwiseFinalOrthogonal, adjoint_adjoint]

theorem partialSum_adjoint (W : ℕ → E →L[𝕜] F) (N : ℕ) :
    partialSum (fun n ↦ (W n)†) N = (partialSum W N)† := by
  apply (eq_adjoint_iff _ _).2
  intro y x
  simp only [partialSum_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact adjoint_inner_left (W i) x y

private theorem summable_apply_of_orthogonal_of_bound (W : ℕ → E →L[𝕜] F)
    (horth : PairwiseFinalOrthogonal W)
    (hbound : ∀ N x, ‖partialSum W N x‖ ≤ ‖x‖) (x : E) :
    Summable (fun n ↦ W n x) := by
  let V : ℕ → Submodule 𝕜 F := fun n ↦ 𝕜 ∙ W n x
  have hVpair : Pairwise ((· ⟂ ·) on V) := by
    intro m n hmn
    change V m ⟂ V n
    dsimp only [V]
    rw [Submodule.isOrtho_span]
    intro u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    rw [← adjoint_inner_right]
    have happ := congrArg (fun A : E →L[𝕜] E ↦ A x) (horth hmn)
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun z : E ↦ inner 𝕜 x z) happ
  have hV : OrthogonalFamily 𝕜 (fun n ↦ V n) (fun n ↦ (V n).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise hVpair
  let f : ∀ n, V n := fun n ↦ ⟨W n x, Submodule.mem_span_singleton_self _⟩
  have hsquare : Summable (fun n ↦ ‖f n‖ ^ 2) := by
    apply summable_of_sum_range_le (c := ‖x‖ ^ 2) (fun n ↦ sq_nonneg ‖f n‖)
    intro N
    rw [← hV.norm_sum f (Finset.range N)]
    have hb : ‖∑ n ∈ Finset.range N, (V n).subtypeₗᵢ (f n)‖ ≤ ‖x‖ := by
      simpa [partialSum, V, f] using hbound N x
    exact (sq_le_sq₀
      (norm_nonneg (∑ n ∈ Finset.range N, (V n).subtypeₗᵢ (f n)))
      (norm_nonneg x)).2 hb
  simpa [V, f] using (hV.summable_iff_norm_sq_summable f).2 hsquare

/-- A pointwise-bounded orthogonal operator series has a bounded strong sum.
No operator-norm convergence is asserted. -/
theorem exists_strongLimit_of_orthogonal_of_bound (W : ℕ → E →L[𝕜] F)
    (horth : PairwiseFinalOrthogonal W)
    (hbound : ∀ N x, ‖partialSum W N x‖ ≤ ‖x‖) :
    ∃ S : E →L[𝕜] F,
      StronglyConverges (partialSum W) atTop S ∧ ‖S‖ ≤ 1 := by
  let f : E → F := fun x ↦ ∑' n, W n x
  have hlim : Tendsto (fun N x ↦ partialSum W N x) atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro x
    simpa [f, partialSum] using
      (summable_apply_of_orthogonal_of_bound W horth hbound x).hasSum.tendsto_sum_nat
  have hnorm : ∀ N, ‖partialSum W N‖ ≤ 1 := fun N ↦
    (partialSum W N).opNorm_le_bound zero_le_one fun x ↦ by
      simpa using hbound N x
  have hrange : Bornology.IsBounded (Set.range (partialSum W)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨1, fun A hA ↦ by rcases hA with ⟨N, rfl⟩; exact hnorm N⟩
  let S : E →L[𝕜] F := ofTendstoOfBoundedRange f (partialSum W) hlim hrange
  refine ⟨S, ?_, ?_⟩
  · intro x
    simpa [S] using tendsto_pi_nhds.1 hlim x
  · apply S.opNorm_le_bound zero_le_one
    intro x
    have hx : Tendsto (fun N ↦ ‖partialSum W N x‖) atTop (𝓝 ‖S x‖) :=
      (show StronglyConverges (partialSum W) atTop S from fun y ↦ by
        simpa [S] using tendsto_pi_nhds.1 hlim y) x |>.norm
    simpa using le_of_tendsto hx (Eventually.of_forall fun N ↦ hbound N x)

theorem norm_partialSum_le_of_adjoint_comp_eq_complement
    (W : ℕ → E →L[𝕜] F) (U : ℕ → Submodule 𝕜 E)
    [∀ N, (U N).HasOrthogonalProjection]
    (hprod : ∀ N, (partialSum (fun n ↦ (W n)†) N).comp (partialSum W N) =
      1 - (U N).starProjection) :
    ∀ N x, ‖partialSum W N x‖ ≤ ‖x‖ := by
  intro N x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [apply_norm_sq_eq_inner_adjoint_left, ← partialSum_adjoint, hprod,
    ← Submodule.starProjection_orthogonal',
    Submodule.re_inner_starProjection_eq_normSq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    ((U N)ᗮ.norm_starProjection_apply_le x)

/-- Strong shell-sum theorem.  Both the operator and adjoint series are
constructed separately; finite defect identities then pass to the two strong
products. -/
theorem exists_strongSums_adjoint_products
    (W : ℕ → E →L[𝕜] F)
    (U : ℕ → Submodule 𝕜 E) (V : ℕ → Submodule 𝕜 F)
    [∀ N, (U N).HasOrthogonalProjection]
    [∀ N, (V N).HasOrthogonalProjection]
    [(⨅ N, U N).HasOrthogonalProjection]
    [(⨅ N, V N).HasOrthogonalProjection]
    (hU : Antitone U) (hV : Antitone V)
    (hi : PairwiseInitialOrthogonal W) (hf : PairwiseFinalOrthogonal W)
    (hprodU : ∀ N, (partialSum (fun n ↦ (W n)†) N).comp (partialSum W N) =
      1 - (U N).starProjection)
    (hprodV : ∀ N, (partialSum W N).comp (partialSum (fun n ↦ (W n)†) N) =
      1 - (V N).starProjection) :
    ∃ S : E →L[𝕜] F, ∃ T : F →L[𝕜] E,
      StronglyConverges (partialSum W) atTop S ∧
      StronglyConverges (partialSum fun n ↦ (W n)†) atTop T ∧
      ‖S‖ ≤ 1 ∧ ‖T‖ ≤ 1 ∧ T = S† ∧
      S†.comp S = 1 - (⨅ N, U N).starProjection ∧
      S.comp (S†) = 1 - (⨅ N, V N).starProjection := by
  have hbW := norm_partialSum_le_of_adjoint_comp_eq_complement W U hprodU
  have hbA := norm_partialSum_le_of_adjoint_comp_eq_complement
    (fun n ↦ (W n)†) V (by simpa [partialSum_adjoint] using hprodV)
  obtain ⟨S, hS, hSnorm⟩ := exists_strongLimit_of_orthogonal_of_bound W hf hbW
  obtain ⟨T, hT, hTnorm⟩ := exists_strongLimit_of_orthogonal_of_bound
    (fun n ↦ (W n)†) (pairwiseFinalOrthogonal_adjoint_iff W |>.2 hi) hbA
  have hAdj : T = S† := adjoint_eq_of_stronglyConverges hS hT fun N ↦
    partialSum_adjoint W N
  have hTU : T.comp S = 1 - (⨅ N, U N).starProjection := by
    apply ext
    intro x
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact (StronglyConverges.comp_of_uniformlyBounded (l := atTop) hT hS 1 fun N ↦ by
        exact (partialSum (fun n ↦ (W n)†) N).opNorm_le_bound zero_le_one fun y ↦ by
          simpa using hbA N y) x
    · have hdefect := (StronglyConverges.const (ι := ℕ) (l := atTop)
        (1 : E →L[𝕜] E)).sub (Submodule.stronglyConverges_starProjection_iInf U hU)
      simpa [hprodU] using hdefect x
  have hSV : S.comp T = 1 - (⨅ N, V N).starProjection := by
    apply ext
    intro x
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · exact (StronglyConverges.comp_of_uniformlyBounded (l := atTop) hS hT 1 fun N ↦ by
        exact (partialSum W N).opNorm_le_bound zero_le_one fun y ↦ by
          simpa using hbW N y) x
    · have hdefect := (StronglyConverges.const (ι := ℕ) (l := atTop)
        (1 : F →L[𝕜] F)).sub (Submodule.stronglyConverges_starProjection_iInf V hV)
      simpa [hprodV] using hdefect x
  exact ⟨S, T, hS, hT, hSnorm, hTnorm, hAdj,
    by simpa [← hAdj] using hTU, by simpa [← hAdj] using hSV⟩

end ContinuousLinearMap
