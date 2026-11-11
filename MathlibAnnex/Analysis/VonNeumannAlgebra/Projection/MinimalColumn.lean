/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The scalar-corner input and arbitrary orthogonal atom family are reused from
the supplied TypeI/MinimalCorner and TypeI/OrthogonalAtoms modules.  The norm
calculation and compression detection below are new proofs on those actual
carriers.  Strong convergence has the existing explicit pointwise meaning.
-/

import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.MinimalCorner
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.OrthogonalAtoms
import MathlibAnnex.Analysis.InnerProductSpace.StrongOperator

/-!
# Norm convergence on a minimal-domain column

For a minimal internal projection `e`, the left ideal `M e = {y | y * e = y}`
is normed by evaluation at any unit vector fixed by `e`.  The represented
range of `e` need not be one-dimensional: its multiplicity is unrestricted.

The final detection theorem applies to the actual compression `U* e U`.
The closed-span formula for the existing supremum of the atom family detects
a nonzero compression directly.  No normality hypothesis on an auxiliary
positive map is introduced.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra InnerProduct

namespace VonNeumannAlgebra

universe u v w

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A nonzero internal minimal projection fixes a unit vector in the
original represented Hilbert space. -/
theorem exists_unit_fixed_vector_of_minimal_projection
    (M : VonNeumannAlgebra K) {e : M.toStarSubalgebra}
    (he : IsMinimalStarProjection e) :
    ∃ η : K, (e : K →L[ℂ] K) η = η ∧ ‖η‖ = 1 := by
  classical
  have hsome : ¬ ∀ ξ : K, (e : K →L[ℂ] K) ξ = 0 := by
    intro h
    apply he.ne_zero
    apply Subtype.ext
    exact ContinuousLinearMap.ext h
  obtain ⟨ξ, hξ⟩ := not_forall.mp hsome
  let ζ : K := (e : K →L[ℂ] K) ξ
  have hζ : ζ ≠ 0 := hξ
  have hζnorm : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ
  have hfix : (e : K →L[ℂ] K) ζ = ζ :=
    congrArg (fun a : M.toStarSubalgebra ↦ (a : K →L[ℂ] K) ξ)
      he.isStarProjection.isIdempotentElem.eq
  let η : K := ((‖ζ‖⁻¹ : ℝ) : ℂ) • ζ
  refine ⟨η, ?_, ?_⟩
  · simp only [η, map_smul, hfix]
  · calc
      ‖η‖ = |‖ζ‖⁻¹| * ‖ζ‖ := by
        simp only [η, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖ζ‖⁻¹ * ‖ζ‖ := by
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ζ))]
      _ = 1 := inv_mul_cancel₀ hζnorm

/-- Evaluation at a fixed unit vector is isometric on the column `M e`.
Minimality is internal to `M`; there is no ambient rank-one hypothesis. -/
theorem norm_eq_apply_of_mem_minimal_column
    (M : VonNeumannAlgebra K) {e : M.toStarSubalgebra}
    (he : IsMinimalStarProjection e) {η : K}
    (heη : (e : K →L[ℂ] K) η = η) (hη : ‖η‖ = 1)
    {y : M.toStarSubalgebra} (hy : y * e = y) :
    ‖(y : K →L[ℂ] K)‖ = ‖(y : K →L[ℂ] K) η‖ := by
  have heStar : e * star y = star y := by
    simpa only [star_mul, he.isStarProjection.isSelfAdjoint.star_eq] using
      congrArg star hy
  have hcorner : e * (star y * y) * e = star y * y := by
    calc
      e * (star y * y) * e = (e * star y) * (y * e) := by
        simp only [mul_assoc]
      _ = star y * y := by rw [heStar, hy]
  obtain ⟨c, hc⟩ := exists_scalar_corner_of_minimal_projection M he (star y * y)
  rw [hcorner] at hc
  have hc' : star (y : K →L[ℂ] K) * (y : K →L[ℂ] K) =
      c • (e : K →L[ℂ] K) :=
    congrArg (fun a : M.toStarSubalgebra ↦ (a : K →L[ℂ] K)) hc
  have he' : IsStarProjection (e : K →L[ℂ] K) :=
    he.isStarProjection.map M.toStarSubalgebra.subtype
  have henorm : ‖(e : K →L[ℂ] K)‖ = 1 := by
    apply le_antisymm (IsStarProjection.norm_le _ he')
    simpa only [heη, hη, mul_one] using (e : K →L[ℂ] K).le_opNorm η
  have happ : (y : K →L[ℂ] K).adjoint ((y : K →L[ℂ] K) η) = c • η := by
    change (star (y : K →L[ℂ] K) * (y : K →L[ℂ] K)) η = c • η
    rw [hc']
    simp only [ContinuousLinearMap.smul_apply, heη]
  have hinner : inner ℂ ((y : K →L[ℂ] K) η) ((y : K →L[ℂ] K) η) = c := by
    rw [← (y : K →L[ℂ] K).adjoint_inner_right η ((y : K →L[ℂ] K) η),
      happ, inner_smul_right, inner_self_eq_norm_sq_to_K, hη]
    simp
  have hcnorm : ‖c‖ = ‖(y : K →L[ℂ] K) η‖ ^ 2 := by
    rw [← hinner, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg _)]
  have hsquare : ‖(y : K →L[ℂ] K)‖ ^ 2 = ‖(y : K →L[ℂ] K) η‖ ^ 2 := by
    calc
      ‖(y : K →L[ℂ] K)‖ ^ 2 =
          ‖star (y : K →L[ℂ] K) * (y : K →L[ℂ] K)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖c‖ := by rw [hc', norm_smul, henorm, mul_one]
      _ = ‖(y : K →L[ℂ] K) η‖ ^ 2 := hcnorm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

/-- A strongly null net in an internal minimal-domain column converges
in operator norm. No uniform boundedness assumption is needed here. -/
theorem tendsto_zero_of_stronglyConverges_minimal_column
    (M : VonNeumannAlgebra K) {e : M.toStarSubalgebra}
    (he : IsMinimalStarProjection e) {ι : Type w} {l : Filter ι}
    (y : ι → M.toStarSubalgebra) (hy : ∀ i, y i * e = y i)
    (hstrong : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (y i : K →L[ℂ] K)) l 0) :
    Tendsto (fun i ↦ (y i : K →L[ℂ] K)) l (𝓝 0) := by
  obtain ⟨η, heη, hη⟩ := exists_unit_fixed_vector_of_minimal_projection M he
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpoint : Tendsto (fun i ↦ ‖(y i : K →L[ℂ] K) η‖) l (𝓝 0) := by
    simpa only [ContinuousLinearMap.zero_apply, norm_zero] using (hstrong η).norm
  have hnorm : (fun i ↦ ‖(y i : K →L[ℂ] K)‖) =
      (fun i ↦ ‖(y i : K →L[ℂ] K) η‖) :=
    funext fun i ↦ norm_eq_apply_of_mem_minimal_column M he heη hη (hy i)
  rw [hnorm]
  exact hpoint

/-- The same equivalence of limits holds at every point of the column. -/
theorem tendsto_of_stronglyConverges_minimal_column
    (M : VonNeumannAlgebra K) {e : M.toStarSubalgebra}
    (he : IsMinimalStarProjection e) {ι : Type w} {l : Filter ι}
    (y : ι → M.toStarSubalgebra) {z : M.toStarSubalgebra}
    (hy : ∀ i, y i * e = y i) (hz : z * e = z)
    (hstrong : ContinuousLinearMap.StronglyConverges
      (fun i ↦ (y i : K →L[ℂ] K)) l (z : K →L[ℂ] K)) :
    Tendsto (fun i ↦ (y i : K →L[ℂ] K)) l (𝓝 (z : K →L[ℂ] K)) := by
  have hd : ContinuousLinearMap.StronglyConverges
      (fun i ↦ ((y i - z : M.toStarSubalgebra) : K →L[ℂ] K)) l 0 := by
    change ContinuousLinearMap.StronglyConverges (fun i ↦ (y i : K →L[ℂ] K) - (z : K →L[ℂ] K)) l 0
    simpa only [sub_self] using
      hstrong.sub (ContinuousLinearMap.StronglyConverges.const (z : K →L[ℂ] K))
  have hn := tendsto_zero_of_stronglyConverges_minimal_column M he
    (fun i ↦ y i - z) (fun i ↦ by rw [sub_mul, hy i, hz]) hd
  have ha := hn.add_const (z : K →L[ℂ] K)
  change Tendsto (fun i ↦ ((y i : K →L[ℂ] K) - (z : K →L[ℂ] K)) + (z : K →L[ℂ] K)) l (𝓝 (0 + (z : K →L[ℂ] K))) at ha
  simpa only [zero_add, sub_add_cancel] using ha

/-- A nonzero concrete compression detects one projection in every family
whose existing projection supremum is one. This uses the actual range-span
formula, and does not assume normality of an unrelated positive map. -/
theorem exists_projection_compression_ne_zero_of_iSupProjection_eq_one
    (M : VonNeumannAlgebra K) {ι : Type w}
    (p : ι → M.toStarSubalgebra) (hp : ∀ i, IsStarProjection (p i))
    (hsup : iSupProjection M p hp = 1)
    (U : H →L[ℂ] K) (hU : U ≠ 0) :
    ∃ i, U.adjoint ∘L (p i : K →L[ℂ] K) ∘L U ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ i, U.adjoint ∘L (p i : K →L[ℂ] K) ∘L U = 0 := by
    simpa only [not_exists, not_not] using h
  have hkill (i : ι) : (p i : K →L[ℂ] K) ∘L U = 0 := by
    apply ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp
    have hpi : IsStarProjection (p i : K →L[ℂ] K) :=
      (hp i).map M.toStarSubalgebra.subtype
    have hpi' : (p i : K →L[ℂ] K).adjoint ∘L (p i : K →L[ℂ] K) =
        (p i : K →L[ℂ] K) := by
      change star (p i : K →L[ℂ] K) * (p i : K →L[ℂ] K) = _
      rw [hpi.isSelfAdjoint.star_eq, hpi.isIdempotentElem.eq]
    calc
      ((p i : K →L[ℂ] K) ∘L U).adjoint ∘L ((p i : K →L[ℂ] K) ∘L U) =
          U.adjoint ∘L ((p i : K →L[ℂ] K).adjoint ∘L (p i : K →L[ℂ] K)) ∘L U := by
        simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
      _ = U.adjoint ∘L (p i : K →L[ℂ] K) ∘L U := by rw [hpi']
      _ = 0 := hzero i
  apply hU
  apply ContinuousLinearMap.ext
  intro ξ
  let J : Submodule ℂ K := (innerSL ℂ (U ξ)).ker
  have hrange (i : ι) : (p i : K →L[ℂ] K).range ≤ J := by
    rintro η ⟨ζ, rfl⟩
    change inner ℂ (U ξ) ((p i : K →L[ℂ] K) ζ) = 0
    have hpi : IsStarProjection (p i : K →L[ℂ] K) :=
      (hp i).map M.toStarSubalgebra.subtype
    have hpoint : (p i : K →L[ℂ] K) (U ξ) = 0 :=
      congrArg (fun T : H →L[ℂ] K ↦ T ξ) (hkill i)
    rw [← (p i : K →L[ℂ] K).adjoint_inner_left ζ (U ξ)]
    simpa only [← ContinuousLinearMap.star_eq_adjoint,
      hpi.isSelfAdjoint.star_eq, hpoint, inner_zero_left]
  have hclosure : (⨆ i, (p i : K →L[ℂ] K).range).topologicalClosure ≤ J := by
    apply Submodule.topologicalClosure_minimal
    · exact iSup_le hrange
    · exact (innerSL ℂ (U ξ)).isClosed_ker
  have hall : (iSupProjection M p hp : K →L[ℂ] K).range ≤ J := by
    rw [range_iSupProjection]
    exact hclosure
  rw [hsup] at hall
  have hself : inner ℂ (U ξ) (U ξ) = 0 :=
    hall (show U ξ ∈ (1 : K →L[ℂ] K).range from ⟨U ξ, rfl⟩)
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp hself

/-- A nonzero concrete compression of a type I factor detects an actual
internal minimal projection, even in a representation with multiplicity. -/
theorem IsFactor.exists_minimal_projection_compression_ne_zero
    {M : VonNeumannAlgebra K} (hM : M.IsFactor) (hI : M.IsTypeI)
    (U : H →L[ℂ] K) (hU : U ≠ 0) :
    ∃ e : M.toStarSubalgebra, IsMinimalStarProjection e ∧
      U.adjoint ∘L (e : K →L[ℂ] K) ∘L U ≠ 0 := by
  classical
  obtain ⟨p, hp, hpmin, s, hps, hs, horth, hatom, hsup⟩ :=
    hM.exists_orthogonal_abelian_atoms hI
  obtain ⟨v, hv⟩ := exists_projection_compression_ne_zero_of_iSupProjection_eq_one M
    (fun v : s ↦ (v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra))
    (fun v ↦ (hs v.1 v.2).1.isStarProjection_mul_star_self) hsup U hU
  exact ⟨(v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra),
    (hatom v.1 v.2).2, hv⟩

/-- The isometric-compression form keeps the nonzero test vector explicit,
so the zero Hilbert-space case is never silently discarded. -/
theorem IsFactor.exists_minimal_projection_compression_ne_zero_of_isometry
    {M : VonNeumannAlgebra K} (hM : M.IsFactor) (hI : M.IsTypeI)
    (U : H →ₗᵢ[ℂ] K) {ξ : H} (hξ : ξ ≠ 0) :
    ∃ e : M.toStarSubalgebra, IsMinimalStarProjection e ∧
      U.toContinuousLinearMap.adjoint ∘L (e : K →L[ℂ] K) ∘L
        U.toContinuousLinearMap ≠ 0 := by
  apply hM.exists_minimal_projection_compression_ne_zero hI U.toContinuousLinearMap
  intro hU
  have hz : U ξ = 0 := congrArg (fun T : H →L[ℂ] K ↦ T ξ) hU
  exact hξ (U.injective (by simpa only [map_zero] using hz))

end VonNeumannAlgebra
