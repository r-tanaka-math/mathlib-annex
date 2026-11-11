/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The pointwise summability argument generalizes the countable construction in
MathlibAnnex/Analysis/InnerProductSpace/OrthogonalSum.lean at commit
5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e.  Here the index is arbitrary and the
convergence filter is the finite-subset net.  The existing strong-product and
adjoint-limit lemmas are imported unchanged.
-/

import MathlibAnnex.Analysis.CStarAlgebra.ProjectionEquivalence
import MathlibAnnex.Analysis.InnerProductSpace.OrthogonalSum
import MathlibAnnex.Analysis.VonNeumannAlgebra.Generated

/-!
# Arbitrary orthogonal sums inside a von Neumann algebra

Both initial and final orthogonality are used.  The operators and their
adjoints are summed separately along all finite subsets; a bounded strong
product argument then proves the partial-isometry identity of the limit.
No countability or separability hypothesis is imposed.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators Function InnerProduct

universe u v w

namespace ContinuousLinearMap

section GeneralOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {ι : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Bounded finite sums of orthogonal operator values give a summable
family at each vector, even for an uncountable index type. -/
theorem summable_apply_of_orthogonal_of_finset_bound
    (W : ι → E →L[𝕜] F)
    (horth : Pairwise (fun i j ↦ (W i)†.comp (W j) = 0))
    (hbound : ∀ s : Finset ι, ∀ x : E, ‖(∑ i ∈ s, W i) x‖ ≤ ‖x‖)
    (x : E) : Summable (fun i ↦ W i x) := by
  classical
  let V : ι → Submodule 𝕜 F := fun i ↦ 𝕜 ∙ W i x
  have hVpair : Pairwise ((· ⟂ ·) on V) := by
    intro i j hij
    change V i ⟂ V j
    dsimp only [V]
    rw [Submodule.isOrtho_span]
    intro a ha b hb
    simp only [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    rw [← adjoint_inner_right]
    have happ := congrArg (fun T : E →L[𝕜] E ↦ T x) (horth hij)
    simpa only [comp_apply, zero_apply, inner_zero_right] using
      congrArg (fun y : E ↦ inner 𝕜 x y) happ
  have hV : OrthogonalFamily 𝕜 (fun i ↦ V i) (fun i ↦ (V i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise hVpair
  let f : ∀ i, V i := fun i ↦ ⟨W i x, Submodule.mem_span_singleton_self _⟩
  have hsquare : Summable (fun i ↦ ‖f i‖ ^ 2) := by
    apply summable_of_sum_le (c := ‖x‖ ^ 2) (fun i ↦ sq_nonneg ‖f i‖)
    intro s
    rw [← hV.norm_sum f s]
    have hb : ‖∑ i ∈ s, (V i).subtypeₗᵢ (f i)‖ ≤ ‖x‖ := by
      simpa [V, f] using hbound s x
    exact (sq_le_sq₀
      (norm_nonneg (∑ i ∈ s, (V i).subtypeₗᵢ (f i))) (norm_nonneg x)).2 hb
  simpa [V, f] using (hV.summable_iff_norm_sq_summable f).2 hsquare

/-- The finite-subset net of a pointwise contractive orthogonal family has
a contractive strong limit. -/
theorem exists_strong_limit_finset_of_orthogonal_of_bound
    (W : ι → E →L[𝕜] F)
    (horth : Pairwise (fun i j ↦ (W i)†.comp (W j) = 0))
    (hbound : ∀ s : Finset ι, ∀ x : E, ‖(∑ i ∈ s, W i) x‖ ≤ ‖x‖) :
    ∃ S : E →L[𝕜] F,
      StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, W i) atTop S ∧ ‖S‖ ≤ 1 := by
  classical
  let f : E → F := fun x ↦ ∑' i, W i x
  have hlim : Tendsto
      (fun s : Finset ι ↦ fun x : E ↦ (∑ i ∈ s, W i) x) atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro x
    simpa [f, HasSum] using
      (summable_apply_of_orthogonal_of_finset_bound W horth hbound x).hasSum
  have hnorm : ∀ s : Finset ι, ‖∑ i ∈ s, W i‖ ≤ 1 := fun s ↦
    (∑ i ∈ s, W i).opNorm_le_bound zero_le_one fun x ↦ by
      simpa only [one_mul] using hbound s x
  have hrange : Bornology.IsBounded (Set.range (fun s : Finset ι ↦ ∑ i ∈ s, W i)) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨1, fun T hT ↦ by rcases hT with ⟨s, rfl⟩; exact hnorm s⟩
  let S : E →L[𝕜] F :=
    ofTendstoOfBoundedRange f (fun s : Finset ι ↦ ∑ i ∈ s, W i) hlim hrange
  have hS : StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, W i) atTop S := by
    intro x
    simpa [S] using tendsto_pi_nhds.1 hlim x
  refine ⟨S, hS, ?_⟩
  apply S.opNorm_le_bound zero_le_one
  intro x
  have hx : Tendsto (fun s : Finset ι ↦ ‖(∑ i ∈ s, W i) x‖) atTop (𝓝 ‖S x‖) :=
    (hS x).norm
  simpa only [one_mul] using le_of_tendsto hx (Eventually.of_forall fun s ↦ hbound s x)

end GeneralOperators

section PartialIsometries

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} {ι : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- An arbitrary doubly orthogonal family of partial isometries has a
partial-isometry strong sum. The initial and final projections are the
strong sums of the corresponding projection families. -/
theorem exists_strong_sum_of_pairwise_orthogonal_partial_isometries
    (V : ι → H →L[𝕜] H) (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    ∃ S : H →L[𝕜] H, IsPartialIsometry S ∧
      StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, V i) atTop S ∧
      StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, star (V i)) atTop (star S) ∧
      ‖S‖ ≤ 1 ∧
      StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, star (V i) * V i)
        atTop (star S * S) ∧
      StronglyConverges (fun s : Finset ι ↦ ∑ i ∈ s, V i * star (V i))
        atTop (S * star S) := by
  classical
  have hsum (s : Finset ι) : IsPartialIsometry (∑ i ∈ s, V i) :=
    IsPartialIsometry.sum s V (fun i _ ↦ hV i)
      (fun _ _ _ _ hij ↦ hi hij) (fun _ _ _ _ hij ↦ hf hij)
  have hnorm (s : Finset ι) : ‖∑ i ∈ s, V i‖ ≤ 1 := (hsum s).norm_le_one
  have hnormStar (s : Finset ι) : ‖∑ i ∈ s, star (V i)‖ ≤ 1 := by
    rw [← star_sum, norm_star]
    exact hnorm s
  have hbound (s : Finset ι) (x : H) : ‖(∑ i ∈ s, V i) x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using (∑ i ∈ s, V i).le_of_opNorm_le (hnorm s) x
  have hboundStar (s : Finset ι) (x : H) : ‖(∑ i ∈ s, star (V i)) x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using
      (∑ i ∈ s, star (V i)).le_of_opNorm_le (hnormStar s) x
  have hi' : Pairwise (fun i j ↦ (V i)†.comp (V j) = 0) := hi
  have hf' : Pairwise (fun i j ↦ (star (V i))†.comp (star (V j)) = 0) := by
    intro i j hij
    simpa only [← star_eq_adjoint, ← mul_def, star_star] using hf hij
  obtain ⟨S, hS, hSnorm⟩ :=
    exists_strong_limit_finset_of_orthogonal_of_bound V hi' hbound
  obtain ⟨T, hT, _⟩ :=
    exists_strong_limit_finset_of_orthogonal_of_bound (fun i ↦ star (V i)) hf' hboundStar
  have hAdj : T = star S := by
    exact adjoint_eq_of_stronglyConverges hS hT (fun s ↦ by
      change (∑ i ∈ s, star (V i)) = star (∑ i ∈ s, V i)
      simp only [star_sum])
  have hSstar : StronglyConverges
      (fun s : Finset ι ↦ star (∑ i ∈ s, V i)) atTop (star S) := by
    simpa only [hAdj, star_sum] using hT
  have hstarNorm (s : Finset ι) : ‖star (∑ i ∈ s, V i)‖ ≤ 1 := by
    rw [star_sum]
    exact hnormStar s
  have hInitial : StronglyConverges
      (fun s : Finset ι ↦ star (∑ i ∈ s, V i) * (∑ i ∈ s, V i))
      atTop (star S * S) := by
    simpa only [← mul_def] using
      StronglyConverges.comp_of_uniformlyBounded hSstar hS 1 hstarNorm
  have hFinal : StronglyConverges
      (fun s : Finset ι ↦ (∑ i ∈ s, V i) * star (∑ i ∈ s, V i))
      atTop (S * star S) := by
    simpa only [← mul_def] using
      StronglyConverges.comp_of_uniformlyBounded hS hSstar 1 hnorm
  have hproductNorm (s : Finset ι) :
      ‖(∑ i ∈ s, V i) * star (∑ i ∈ s, V i)‖ ≤ 1 := by
    calc
      ‖(∑ i ∈ s, V i) * star (∑ i ∈ s, V i)‖ ≤
          ‖∑ i ∈ s, V i‖ * ‖star (∑ i ∈ s, V i)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul (hnorm s) (hstarNorm s) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have htriple :=
    StronglyConverges.comp_of_uniformlyBounded hFinal hS 1 hproductNorm
  have htripleId (s : Finset ι) :
      (∑ i ∈ s, V i) * star (∑ i ∈ s, V i) * (∑ i ∈ s, V i) =
        ∑ i ∈ s, V i := (hsum s).mul_star_self_mul
  have htripleLimit : StronglyConverges
      (fun s : Finset ι ↦ ∑ i ∈ s, V i) atTop (S * star S * S) := by
    simpa only [← mul_def, htripleId] using htriple
  have hpi : IsPartialIsometry S := by
    change S * star S * S = S
    exact ContinuousLinearMap.ext fun x ↦ tendsto_nhds_unique (htripleLimit x) (hS x)
  have hInitialEq (s : Finset ι) :
      star (∑ i ∈ s, V i) * (∑ i ∈ s, V i) = ∑ i ∈ s, star (V i) * V i :=
    IsPartialIsometry.star_sum_mul_sum s V (fun _ _ _ _ hij ↦ hi hij)
  have hFinalEq (s : Finset ι) :
      (∑ i ∈ s, V i) * star (∑ i ∈ s, V i) = ∑ i ∈ s, V i * star (V i) :=
    IsPartialIsometry.sum_mul_star_sum s V (fun _ _ _ _ hij ↦ hf hij)
  exact ⟨S, hpi, hS, by simpa only [hAdj] using hT, hSnorm,
    by simpa only [hInitialEq] using hInitial,
    by simpa only [hFinalEq] using hFinal⟩

end PartialIsometries

end ContinuousLinearMap

namespace VonNeumannAlgebra

variable {H : Type u} {ι : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The arbitrary orthogonal sum belongs to the specified algebra.  Its
witness is returned in the subtype, rather than only in ambient `B(H)`. -/
theorem exists_orthogonal_sum_partial_isometry
    (M : VonNeumannAlgebra H) (V : ι → M.toStarSubalgebra)
    (hV : ∀ i, IsPartialIsometry (V i))
    (hi : Pairwise (fun i j ↦ star (V i) * V j = 0))
    (hf : Pairwise (fun i j ↦ V i * star (V j) = 0)) :
    ∃ S : M.toStarSubalgebra, IsPartialIsometry S ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, (V i : H →L[ℂ] H)) atTop (S : H →L[ℂ] H) ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, star (V i : H →L[ℂ] H))
        atTop (star (S : H →L[ℂ] H)) ∧
      ‖(S : H →L[ℂ] H)‖ ≤ 1 ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, star (V i : H →L[ℂ] H) * (V i : H →L[ℂ] H))
        atTop (star (S : H →L[ℂ] H) * (S : H →L[ℂ] H)) ∧
      ContinuousLinearMap.StronglyConverges
        (fun s : Finset ι ↦ ∑ i ∈ s, (V i : H →L[ℂ] H) * star (V i : H →L[ℂ] H))
        atTop ((S : H →L[ℂ] H) * star (S : H →L[ℂ] H)) := by
  classical
  let W : ι → H →L[ℂ] H := fun i ↦ V i
  have hW (i : ι) : IsPartialIsometry (W i) :=
    (hV i).map M.toStarSubalgebra.subtype
  have hiW : Pairwise (fun i j ↦ star (W i) * W j = 0) := by
    intro i j hij
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) (hi hij)
  have hfW : Pairwise (fun i j ↦ W i * star (W j) = 0) := by
    intro i j hij
    exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) (hf hij)
  obtain ⟨S, hpi, hS, hSstar, hnorm, hInitial, hFinal⟩ :=
    ContinuousLinearMap.exists_strong_sum_of_pairwise_orthogonal_partial_isometries
      W hW hiW hfW
  have hmem : S ∈ M := M.mem_of_stronglyConverges
    (fun s ↦ M.toStarSubalgebra.sum_mem (fun i _ ↦ (V i).property)) hS
  let S' : M.toStarSubalgebra := ⟨S, hmem⟩
  have hpi' : IsPartialIsometry S' := by
    apply Subtype.ext
    exact hpi
  exact ⟨S', hpi', hS, hSstar, hnorm, hInitial, hFinal⟩

end VonNeumannAlgebra
