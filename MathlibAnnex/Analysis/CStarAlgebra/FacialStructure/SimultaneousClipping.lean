/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SimultaneousExactInterpolation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Sharp self-adjoint and positive simultaneous interpolation

Before clipping, the coarse exact theorem is applied to the finite
compression on `E_i + T_i(E_i)`. Both products with the projection are then
proved equal to that compression. The pinned generic reducing-corner CFC
lemma preserves this equality. Clipping is performed by nonunital CFC in
the original algebra, with the vanishing-at-zero condition proved explicitly.
No rank-one preimage or unitality of the source algebra is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {I : Type v} [Fintype I] {H : I → Type w}
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Coarse exact interpolation on the reducing finite enlargement. Both
corner identities are established before functional calculus is applied. -/
theorem exists_selfAdjoint_norm_le_two_mul_forall_finiteReduction
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 2 * C ∧ ∀ i,
      pi i a * (finiteReduction (E i) (T i)).starProjection = finiteCompression (E i) (T i) ∧
      (finiteReduction (E i) (T i)).starProjection * pi i a = finiteCompression (E i) (T i) := by
  let F : ∀ i, Submodule ℂ (H i) := fun i => finiteReduction (E i) (T i)
  let S : ∀ i, H i →L[ℂ] H i := fun i => finiteCompression (E i) (T i)
  have hS (i : I) : IsSelfAdjoint (S i) := isSelfAdjoint_finiteCompression (E i) (T i) (hT i)
  have hSnorm (i : I) : ‖S i‖ ≤ C := (norm_finiteCompression_le (E i) (T i)).trans (hTC i)
  obtain ⟨a, ha, hanorm, hexact⟩ :=
    exists_selfAdjoint_norm_le_two_mul_forall_sub_mul_starProjection_eq_zero
      pi hirr hne F S hS C hC hSnorm
  refine ⟨a, ha, hanorm, fun i => ?_⟩
  have hsupport := finiteCompression_supported (E i) (T i)
  have hright : pi i a * (F i).starProjection = S i := by
    have hz : S i * (F i).starProjection - pi i a * (F i).starProjection = 0 := by
      simpa only [sub_mul] using hexact i
    exact (sub_eq_zero.mp hz).symm.trans hsupport.2
  have hleft : (F i).starProjection * pi i a = S i := by
    calc
      (F i).starProjection * pi i a = star (pi i a * (F i).starProjection) := by
        rw [star_mul, (ha.map (pi i)).star_eq, (isSelfAdjoint_starProjection (F i)).star_eq]
      _ = star (S i) := by rw [hright]
      _ = S i := (hS i).star_eq
  exact ⟨hright, hleft⟩

/-- A continuous zero-fixing function transports original-algebra functional
calculus through a representation to the unital operator calculus. -/
theorem map_cfcₙ_eq_cfc {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (pi : NonUnitalCStarRepresentation A K) (a : A) (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    pi (cfcₙ f a) = cfc f (pi a) := by
  rw [pi.map_cfcₙ f a hf.continuousOn hf0 (by fun_prop) ha (ha.map pi),
    cfcₙ_eq_cfc hf.continuousOn hf0]

/-- Sharp simultaneous self-adjoint interpolation with a common source norm
budget. Every requested finite-dimensional subspace is treated exactly. -/
theorem exists_selfAdjoint_norm_le_forall_eq_on
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, IsSelfAdjoint (T i))
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ C ∧
      ∀ i, ∀ x : H i, x ∈ E i → pi i a x = T i x := by
  let F : ∀ i, Submodule ℂ (H i) := fun i => finiteReduction (E i) (T i)
  let S : ∀ i, H i →L[ℂ] H i := fun i => finiteCompression (E i) (T i)
  obtain ⟨a, ha, -, hcorner⟩ := exists_selfAdjoint_norm_le_two_mul_forall_finiteReduction
    pi hirr hne E T hT C hC hTC
  let f : ℝ → ℝ := fun t => max (-C) (min C t)
  have hf : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hf0 : f 0 = 0 := by
    simp only [f, min_eq_right hC, max_eq_right (neg_nonpos.mpr hC)]
  have hfnorm (t : ℝ) : ‖f t‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfix (i : I) : cfc f (S i) = S i := by
    letI : Nontrivial (H i) := nontrivial_of_isNonzero (pi i) (hirr i).1
    calc
      cfc f (S i) = cfc (fun t : ℝ => t) (S i) := by
        apply cfc_congr
        intro t ht
        have htnorm : ‖t‖ ≤ C := (spectrum.norm_le_norm_of_mem ht).trans
          ((norm_finiteCompression_le (E i) (T i)).trans (hTC i))
        rw [Real.norm_eq_abs, abs_le] at htnorm
        simp [f, min_eq_right htnorm.2, max_eq_right htnorm.1]
      _ = S i := cfc_id' ℝ (S i)
        (isSelfAdjoint_finiteCompression (E i) (T i) (hT i))
  refine ⟨cfcₙ f a, cfcₙ_predicate (p := IsSelfAdjoint) f a, norm_cfcₙ_le (fun t _ => hfnorm t), ?_⟩
  intro i x hx
  let q : H i →L[ℂ] H i := (F i).starProjection
  have hsupport := finiteCompression_supported (E i) (T i)
  have haq : Commute (pi i a) q := by
    rw [commute_iff_eq]
    exact (hcorner i).1.trans (hcorner i).2.symm
  have hSq : Commute (S i) q := by
    rw [commute_iff_eq]
    exact hsupport.2.trans hsupport.1.symm
  have hfcq : cfc f (pi i a) * q = S i := by
    calc
      cfc f (pi i a) * q = cfc f (S i) * q :=
        cfc_mul_eq_of_mul_eq (ha.map (pi i))
          (isSelfAdjoint_finiteCompression (E i) (T i) (hT i))
          isStarProjection_starProjection haq hSq
          ((hcorner i).1.trans hsupport.2.symm) f hf hf0
      _ = S i := by rw [hfix i, hsupport.2]
  have hxF : x ∈ F i := (show E i ≤ F i from le_sup_left) hx
  have hqx : q x = x := (F i).starProjection_eq_self_iff.mpr hxF
  have heval := congrArg (fun R : H i →L[ℂ] H i => R x) hfcq
  rw [map_cfcₙ_eq_cfc (pi i) a ha f hf hf0]
  simpa [ContinuousLinearMap.mul_apply, hqx, S, finiteCompression_apply_of_mem (E i) (T i) hx]
    using heval

/-- Sharp positive simultaneous interpolation, with positivity and the norm
budget in the original nonunital algebra. The source order is any compatible
star order, not an additional unitality or representation hypothesis. -/
theorem exists_nonneg_norm_le_forall_eq_on [PartialOrder A] [StarOrderedRing A]
    (pi : ∀ i, NonUnitalCStarRepresentation A (H i))
    (hirr : ∀ i, (pi i).IsIrreducible)
    (hne : ∀ i k, i ≠ k → ¬ (pi i).UnitaryEquivalent (pi k))
    (E : ∀ i, Submodule ℂ (H i)) [∀ i, FiniteDimensional ℂ (E i)]
    (T : ∀ i, H i →L[ℂ] H i) (hT : ∀ i, 0 ≤ T i)
    (C : ℝ) (hC : 0 ≤ C) (hTC : ∀ i, ‖T i‖ ≤ C) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ C ∧
      ∀ i, ∀ x : H i, x ∈ E i → pi i a x = T i x := by
  let F : ∀ i, Submodule ℂ (H i) := fun i => finiteReduction (E i) (T i)
  let S : ∀ i, H i →L[ℂ] H i := fun i => finiteCompression (E i) (T i)
  have hTself (i : I) : IsSelfAdjoint (T i) := IsSelfAdjoint.of_nonneg (hT i)
  have hSnonneg (i : I) : 0 ≤ S i := finiteCompression_nonneg (E i) (T i) (hT i)
  obtain ⟨a, ha, -, hcorner⟩ := exists_selfAdjoint_norm_le_two_mul_forall_finiteReduction
    pi hirr hne E T hTself C hC hTC
  let f : ℝ → ℝ := fun t => max 0 (min C t)
  have hf : Continuous f := continuous_const.max (continuous_const.min continuous_id)
  have hf0 : f 0 = 0 := by simp only [f, min_eq_right hC, max_self]
  have hfnonneg (t : ℝ) : 0 ≤ f t := le_max_left _ _
  have hfnorm (t : ℝ) : ‖f t‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg t)]
    exact max_le hC (min_le_left _ _)
  have hfix (i : I) : cfc f (S i) = S i := by
    letI : Nontrivial (H i) := nontrivial_of_isNonzero (pi i) (hirr i).1
    calc
      cfc f (S i) = cfc (fun t : ℝ => t) (S i) := by
        apply cfc_congr
        intro t ht
        have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg (hSnonneg i) ht
        have htC : ‖t‖ ≤ C := (spectrum.norm_le_norm_of_mem ht).trans
          ((norm_finiteCompression_le (E i) (T i)).trans (hTC i))
        rw [Real.norm_eq_abs, abs_of_nonneg ht0] at htC
        simp [f, min_eq_right htC, max_eq_right ht0]
      _ = S i := cfc_id' ℝ (S i) (IsSelfAdjoint.of_nonneg (hSnonneg i))
  refine ⟨cfcₙ f a, cfcₙ_nonneg (fun t _ => hfnonneg t), norm_cfcₙ_le (fun t _ => hfnorm t), ?_⟩
  intro i x hx
  let q : H i →L[ℂ] H i := (F i).starProjection
  have hsupport := finiteCompression_supported (E i) (T i)
  have haq : Commute (pi i a) q := by
    rw [commute_iff_eq]
    exact (hcorner i).1.trans (hcorner i).2.symm
  have hSq : Commute (S i) q := by
    rw [commute_iff_eq]
    exact hsupport.2.trans hsupport.1.symm
  have hfcq : cfc f (pi i a) * q = S i := by
    calc
      cfc f (pi i a) * q = cfc f (S i) * q :=
        cfc_mul_eq_of_mul_eq (ha.map (pi i)) (IsSelfAdjoint.of_nonneg (hSnonneg i))
          isStarProjection_starProjection haq hSq
          ((hcorner i).1.trans hsupport.2.symm) f hf hf0
      _ = S i := by rw [hfix i, hsupport.2]
  have hxF : x ∈ F i := (show E i ≤ F i from le_sup_left) hx
  have hqx : q x = x := (F i).starProjection_eq_self_iff.mpr hxF
  have heval := congrArg (fun R : H i →L[ℂ] H i => R x) hfcq
  rw [map_cfcₙ_eq_cfc (pi i) a ha f hf hf0]
  simpa [ContinuousLinearMap.mul_apply, hqx, S, finiteCompression_apply_of_mem (E i) (T i) hx]
    using heval

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
