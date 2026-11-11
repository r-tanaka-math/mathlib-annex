/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Fintype.EquivFin
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Factor
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeII1
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeDecomposition

/-!
# Finite type I factors and the accepted II₁ predicate

A Hilbert basis with infinite index set admits a proper shift: shift a
countable subset and fix the rest. The associated orthonormal family gives
an isometry on the whole Hilbert space whose range misses one basis vector.
This uses no countability or separability hypothesis on the Hilbert space.

The intrinsic type I factor model then turns finiteness into finite
dimensionality of the algebra. Consequently the accepted finite,
infinite-dimensional factor predicate implies the general type II
predicate. The accepted predicates themselves are unchanged.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace lp CStarAlgebra

namespace ContinuousLinearMap

private theorem exists_proper_self_embedding (ι : Type*) [Infinite ι] :
    ∃ f : ι ↪ ι, ∃ i₀ : ι, ∀ i : ι, f i ≠ i₀ := by
  classical
  let j : ℕ ↪ ι := Infinite.natEmbedding ι
  let f : ι → ι := fun i ↦
    if h : ∃ n : ℕ, j n = i then j (h.choose + 1) else i
  have hf_on (n : ℕ) : f (j n) = j (n + 1) := by
    dsimp only [f]
    split_ifs with h
    · exact congrArg (fun m : ℕ ↦ j (m + 1)) (j.injective h.choose_spec)
    · exact (h ⟨n, rfl⟩).elim
  have hf_off (i : ι) (hi : ¬ ∃ n : ℕ, j n = i) : f i = i := by
    simp only [f, dif_neg hi]
  have hf_inj : Function.Injective f := by
    intro i k hik
    by_cases hi : ∃ n : ℕ, j n = i
    · obtain ⟨m, rfl⟩ := hi
      by_cases hk : ∃ n : ℕ, j n = k
      · obtain ⟨n, rfl⟩ := hk
        exact congrArg j (Nat.add_right_cancel (j.injective (by
          simpa only [hf_on] using hik)))
      · have hmk : j (m + 1) = k := by
          simpa only [hf_on, hf_off k hk] using hik
        exact (hk ⟨m + 1, hmk⟩).elim
    · by_cases hk : ∃ n : ℕ, j n = k
      · obtain ⟨n, rfl⟩ := hk
        have hin : i = j (n + 1) := by
          simpa only [hf_on, hf_off i hi] using hik
        exact (hi ⟨n + 1, hin.symm⟩).elim
      · simpa only [hf_off i hi, hf_off k hk] using hik
  refine ⟨⟨f, hf_inj⟩, j 0, ?_⟩
  intro i h
  change f i = j 0 at h
  by_cases hi : ∃ n : ℕ, j n = i
  · obtain ⟨n, rfl⟩ := hi
    have hn : n + 1 = 0 := j.injective (by simpa only [hf_on] using h)
    exact Nat.succ_ne_zero n hn
  · rw [hf_off i hi] at h
    exact hi ⟨0, h.symm⟩

/-- An infinite-dimensional Hilbert space has a proper isometry. The
construction shifts only a countable subset of an arbitrary Hilbert basis
and fixes its remaining indices; no separability assumption is present. -/
theorem exists_proper_isometry_of_not_finiteDimensional
    (𝕜 : Type*) [RCLike 𝕜] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (hdim : ¬ FiniteDimensional 𝕜 H) :
    ∃ v : H →L[𝕜] H, star v * v = 1 ∧ v * star v ≠ 1 := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis 𝕜 H
  letI : Infinite w := Infinite.of_not_fintype fun hw ↦ by
    letI := hw
    exact hdim b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  obtain ⟨f, i₀, hf⟩ := exists_proper_self_embedding w
  have hv : Orthonormal 𝕜 (fun i : w ↦ b (f i)) :=
    b.orthonormal.comp f f.injective
  let S : H →ₗᵢ[𝕜] H :=
    hv.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry
  have horth (x : H) : inner 𝕜 (b i₀) (S x) = 0 := by
    have hs := (hv.orthogonalFamily.hasSum_linearIsometry (b.repr x)).mapL
      (innerSL 𝕜 (b i₀))
    change HasSum (fun i : w ↦ inner 𝕜 (b i₀) ((b.repr x i) • b (f i)))
      (inner 𝕜 (b i₀) (S x)) at hs
    have hzero (i : w) : inner 𝕜 (b i₀) (b (f i)) = 0 :=
      b.orthonormal.inner_eq_zero (Ne.symm (hf i))
    have hs0 : HasSum (fun _ : w ↦ (0 : 𝕜)) (inner 𝕜 (b i₀) (S x)) := by
      simpa only [inner_smul_right, hzero, mul_zero] using hs
    exact hs0.unique hasSum_zero
  have hnot_surj : ¬ Function.Surjective S := by
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj (b i₀)
    have hzero := horth x
    rw [hx] at hzero
    exact b.orthonormal.ne_zero i₀ (inner_self_eq_zero.mp hzero)
  let v : H →L[𝕜] H := S.toContinuousLinearMap
  refine ⟨v, ?_, ?_⟩
  · change S.toContinuousLinearMap.adjoint ∘L S.toContinuousLinearMap = 1
    exact S.adjoint_comp_self
  · intro hunitary
    apply hnot_surj
    intro x
    refine ⟨star v x, ?_⟩
    have hx := congrArg (fun T : H →L[𝕜] H ↦ T x) hunitary
    change v (star v x) = x at hx
    exact hx

/-- If every isometry of a Hilbert space is unitary, the Hilbert space is
finite-dimensional. This is the contrapositive of the actual proper
isometry construction above. -/
theorem finiteDimensional_of_isometries_unitary
    (𝕜 : Type*) [RCLike 𝕜] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (hfinite : ∀ v : H →L[𝕜] H, star v * v = 1 → v * star v = 1) :
    FiniteDimensional 𝕜 H := by
  classical
  by_contra hdim
  obtain ⟨v, hv, hv'⟩ := exists_proper_isometry_of_not_finiteDimensional 𝕜 H hdim
  exact hv' (hfinite v hv)

end ContinuousLinearMap

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Finiteness of a full operator algebra forces finite-dimensionality of
its Hilbert space. The full-range hypothesis is explicit. -/
theorem finiteDimensional_of_isFinite_of_all_operators_mem
    (M : VonNeumannAlgebra H) (hM : IsFinite M)
    (hfull : ∀ T : H →L[ℂ] H, T ∈ M) : FiniteDimensional ℂ H :=
  ContinuousLinearMap.finiteDimensional_of_isometries_unitary ℂ H
    (fun T hT ↦ hM T (hfull T) hT)

/-- Finiteness transfers across a star-algebra equivalence to a full
operator algebra and therefore makes its model Hilbert space finite
dimensional. This helper is applied below to the constructed intrinsic
factor model. -/
theorem IsFinite.finiteDimensional_of_starAlgEquiv_continuousLinearMap
    {M : VonNeumannAlgebra H} (hM : IsFinite M)
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] (K →L[ℂ] K)) : FiniteDimensional ℂ K := by
  apply ContinuousLinearMap.finiteDimensional_of_isometries_unitary ℂ K
  intro T hT
  let a : M.toStarSubalgebra := e.symm T
  have inj : Function.Injective (fun z : M.toStarSubalgebra => e z) := e.injective
  have hmul (x y : M.toStarSubalgebra) : e (x * y) = e x * e y := e.map_mul' x y
  have hstar (z : M.toStarSubalgebra) : e (star z) = star (e z) := e.map_star' z
  have ha : star a * a = 1 := by
    apply inj
    simpa only [hmul, hstar, a, e.apply_symm_apply, map_one] using hT
  have ha' : a * star a = 1 := Subtype.ext
    (hM (a : H →L[ℂ] H) a.property (congrArg Subtype.val ha))
  have h := congrArg e ha'
  simpa only [hmul, hstar, a, e.apply_symm_apply, map_one] using h

/-- A finite type I factor is finite-dimensional as an algebra. Its Hilbert
space model is produced by the intrinsic factor-model theorem, rather than
assumed as input. The dimension is that of `M.toStarSubalgebra`, not that
of its possibly amplified ambient representation space. -/
theorem finiteDimensional_of_isFactor_of_isFinite_of_isTypeI
    (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (hfinite : IsFinite M) (htype : IsTypeI M) :
    FiniteDimensional ℂ M.toStarSubalgebra := by
  obtain ⟨K, instN, instI, instC, instNT, e, _, _, _⟩ :=
    exists_starAlgEquiv_continuousLinearMap_of_isFactor_of_isTypeI M hfactor htype
  letI := instN
  letI := instI
  letI := instC
  letI := instNT
  letI : FiniteDimensional ℂ K :=
    hfinite.finiteDimensional_of_starAlgEquiv_continuousLinearMap e
  let f : M.toStarSubalgebra →ₗ[ℂ] (K →L[ℂ] K) :=
    { toFun := e
      map_add' := map_add e
      map_smul' := map_smul e }
  exact FiniteDimensional.of_injective f e.injective

/-- The accepted finite infinite-dimensional factor predicate excludes
intrinsic type I. -/
theorem IsTypeII1.not_isTypeI {M : VonNeumannAlgebra H} (hM : IsTypeII1 M) :
    ¬ IsTypeI M := by
  intro hI
  exact hM.2.2
    (finiteDimensional_of_isFactor_of_isFinite_of_isTypeI M hM.1 hM.2.1 hI)

/-- An algebra satisfying the accepted II₁ predicate has no nonzero
internal abelian projection. -/
theorem IsTypeII1.eq_zero_of_abelian_projection
    {M : VonNeumannAlgebra H} (hM : IsTypeII1 M)
    {p : M.toStarSubalgebra} (hp : IsAbelianProjection M p) : p = 0 := by
  classical
  by_contra hp0
  apply hM.not_isTypeI
  exact hM.1.isTypeI_iff_exists_nonzero_abelian_projection.mpr ⟨p, hp, hp0⟩

/-- The accepted II₁ predicate implies the general projection-theoretic
type II predicate. Finiteness supplies semifiniteness, and the finite type
I factor theorem excludes all nonzero abelian projections. -/
theorem IsTypeII1.isTypeII {M : VonNeumannAlgebra H} (hM : IsTypeII1 M) :
    IsTypeII M := by
  refine ⟨hM.2.1.isSemifinite, ?_⟩
  intro p hp _
  exact hM.eq_zero_of_abelian_projection hp

end VonNeumannAlgebra

