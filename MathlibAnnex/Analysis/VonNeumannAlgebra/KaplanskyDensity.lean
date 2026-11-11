/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import MathlibAnnex.Analysis.CStarAlgebra.Kadison
import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant

/-!
# Bounded density in an arbitrary represented bicommutant

Self-adjoint finite-vector approximation is obtained from the general
finite-amplification theorem. The real orthogonal-complement argument tests
two finite families and does not transfer strong convergence to adjoints.
The existing bounded transform and its two-resolvent estimate then give
approximants in the source closed unit ball.

## Source attribution

The self-adjoint density proof adapts
`StarAlgHom.exists_selfAdjoint_atomic_apply_sub_norm_lt_of_irreducible` in
`MathlibAnnex/Analysis/CStarAlgebra/FiniteInterpolation.lean`, at Annex commit
`5cbbf304e651c6c50163a59ba7f9fcf6c22eca4e` (Apache-2.0). Its irreducible
approximation input is replaced by the accepted general finite-amplification
theorem. The cutoff and radial rescaling arguments adapt `Kadison.lean` at
the same commit, reusing its scalar functions and all resolvent estimates.
The pointwise radial and norm-budget proof organization also adapts
`FacialStructure/BoundedApproximation.lean` at that commit; the irreducible
family hypotheses of its theorems are not adopted here.
-/

set_option autoImplicit false

open scoped ENNReal lp ComplexStarModule CStarAlgebra
open Set Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

namespace StarAlgHom

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint element of an arbitrary represented bicommutant admits
self-adjoint simultaneous finite-vector approximation. -/
theorem exists_selfAdjoint_forall_apply_sub_norm_lt_of_mem_bicommutant
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε := by
  classical
  let K := HilbertSum (fun _ : I => H)
  let ρ := atomicRepresentation (fun _ : I => π)
  let x : K := finiteHilbertSum ξ
  let D : K →L[ℂ] K :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  let t : K := D x
  letI : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K
  let L : selfAdjoint A →ₗ[ℝ] K := selfAdjointOrbitMap π ξ
  let M : Submodule ℝ K := LinearMap.range L
  have htclosure : t ∈ M.topologicalClosure := by
    apply (le_of_eq M.orthogonal_orthogonal_eq_closure : Mᗮᗮ ≤ M.topologicalClosure)
    rw [Submodule.mem_orthogonal]
    intro y hy
    have horbit (a : selfAdjoint A) : inner ℝ (L a) y = 0 := by
      exact (M.mem_orthogonal y).mp hy (L a) ⟨a, rfl⟩
    let z : Sum I I → H := Sum.elim ξ (fun i => y i)
    have happrox (m : ℕ) : ∃ b : A,
        ∀ k, ‖π b (z k) - T (z k)‖ < (((m + 1 : ℕ) : ℝ))⁻¹ := by
      apply exists_forall_apply_sub_norm_lt_of_mem_bicommutant π hTmem z
      positivity
    choose b hb using happrox
    have heps : Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))⁻¹)
        atTop (nhds 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcoord (k : Sum I I) :
        Tendsto (fun m => π (b m) (z k)) atTop (nhds (T (z k))) := by
      have hbound (m : ℕ) :
          ‖π (b m) (z k) - T (z k)‖ ≤ (((m + 1 : ℕ) : ℝ))⁻¹ :=
        (hb m k).le
      have hnorm : Tendsto (fun m => ‖π (b m) (z k) - T (z k)‖)
          atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) hbound heps
      have hzero : Tendsto (fun m => π (b m) (z k) - T (z k))
          atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
      convert hzero.add_const (T (z k)) using 1 <;> simp
    have hleft (i : I) :
        Tendsto (fun m => π (b m) (ξ i)) atTop (nhds (T (ξ i))) := by
      simpa [z] using hcoord (Sum.inl i)
    have hright (i : I) :
        Tendsto (fun m => π (b m) (y i)) atTop (nhds (T (y i))) := by
      simpa [z] using hcoord (Sum.inr i)
    have hf : Tendsto (fun m => (inner ℂ (ρ (b m) x) y).re)
        atTop (nhds (inner ℂ t y).re) := by
      have hi (i : I) : Tendsto
          (fun m => (inner ℂ (π (b m) (ξ i)) (y i)).re) atTop
          (nhds (inner ℂ (T (ξ i)) (y i)).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp
          ((hleft i).inner tendsto_const_nhds)
      simpa [K, ρ, x, t, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun i _ => hi i))
    have hg : Tendsto (fun m => (inner ℂ x (ρ (b m) y)).re)
        atTop (nhds (inner ℂ x (D y)).re) := by
      have hi (i : I) : Tendsto
          (fun m => (inner ℂ (ξ i) (π (b m) (y i))).re) atTop
          (nhds (inner ℂ (ξ i) (T (y i))).re) :=
        Complex.continuous_re.continuousAt.tendsto.comp
          (tendsto_const_nhds.inner (hright i))
      simpa [K, ρ, x, D, lp.inner_eq_tsum, tsum_fintype] using
        (tendsto_finsetSum Finset.univ (fun i _ => hi i))
    have hTadj : ContinuousLinearMap.adjoint T = T := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
    have htarget : (inner ℂ x (D y)).re = (inner ℂ t y).re := by
      simp only [K, x, D, t, lp.inner_eq_tsum, tsum_fintype,
        finiteHilbertSum_apply, diagonal_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      calc
        inner ℂ (ξ i) (T (y i)) =
            inner ℂ (ContinuousLinearMap.adjoint T (ξ i)) (y i) :=
          (ContinuousLinearMap.adjoint_inner_left T (y i) (ξ i)).symm
        _ = inner ℂ (T (ξ i)) (y i) := by rw [hTadj]
    have hzero (m : ℕ) :
        (inner ℂ (ρ (realPart (b m) : A) x) y).re = 0 := by
      simpa [L, selfAdjointOrbitMap, ρ, x,
        real_inner_eq_re_inner] using horbit (realPart (b m))
    have hsumzero (m : ℕ) :
        (inner ℂ (ρ (b m) x) y).re +
          (inner ℂ x (ρ (b m) y)).re = 0 := by
      have hs := re_inner_selfAdjointOrbitMap_realPart π ξ (b m) y
      dsimp only at hs
      rw [hzero m] at hs
      norm_num at hs ⊢
      exact hs
    have hsumlim := hf.add hg
    rw [htarget] at hsumlim
    have hzerolim : Tendsto
        (fun m => (inner ℂ (ρ (b m) x) y).re +
          (inner ℂ x (ρ (b m) y)).re) atTop (nhds 0) := by
      simpa only [hsumzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    have hdouble : (inner ℂ t y).re + (inner ℂ t y).re = 0 :=
      tendsto_nhds_unique hsumlim hzerolim
    have hq : (inner ℂ t y).re = 0 := by linarith
    rw [real_inner_eq_re_inner, inner_re_symm]
    exact hq
  change t ∈ closure (M : Set K) at htclosure
  obtain ⟨u, huM, hdist⟩ := Metric.mem_closure_iff.mp htclosure ε hε
  obtain ⟨a, rfl⟩ := huM
  refine ⟨(a : A), a.property, fun i => ?_⟩
  rw [dist_eq_norm] at hdist
  have hnorm : ‖ρ (a : A) x - D x‖ < ε := by
    simpa [L, selfAdjointOrbitMap, ρ, x, t, D, norm_sub_rev] using hdist
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (ρ (a : A) x - D x) i
  exact hcoord.trans_lt hnorm

/-- Strict self-adjoint contractions in the bicommutant can be approximated
by self-adjoint contractions in the original source algebra. -/
theorem exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant_of_norm_lt_one
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T) (hTnorm : ‖T‖ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · letI := hH
    exact ⟨0, IsSelfAdjoint.zero A, by simp, fun i => by
      simpa only [Subsingleton.elim (π 0 (ξ i)) (T (ξ i)), sub_self, norm_zero] using hε⟩
  · letI := hH
    let S : H →L[ℂ] H := strictContractionPreimage T
    have hS : IsSelfAdjoint S := isSelfAdjoint_strictContractionPreimage T
    have hSmem : S ∈ Set.centralizer (Set.centralizer (Set.range π)) := by
      change cfc strictContractionPreimageScalar T ∈
        (VonNeumannAlgebra.generated π.range).toStarSubalgebra
      exact cfc_mem (𝕜' := ℂ) strictContractionPreimageScalar hTmem
    let η : Sum I I → H := Sum.elim
      (fun i => lowerSelfAdjointResolvent S (ξ i))
      (fun i => upperSelfAdjointResolvent S (ξ i))
    obtain ⟨b, hbself, hb⟩ :=
      π.exists_selfAdjoint_forall_apply_sub_norm_lt_of_mem_bicommutant
        η S hSmem hS (half_pos hε)
    refine ⟨boundedSelfAdjointTransform b,
      isSelfAdjoint_boundedSelfAdjointTransform hbself,
      norm_boundedSelfAdjointTransform_le_one b, fun i => ?_⟩
    have hpreimage : boundedSelfAdjointTransform S = T :=
      boundedSelfAdjointTransform_strictContractionPreimage hT hTnorm
    have hcoord (k : Sum I I) : ‖(S - π b) (η k)‖ < ε / 2 := by
      simpa only [ContinuousLinearMap.sub_apply, norm_sub_rev] using hb k
    rw [π.map_boundedSelfAdjointTransform b hbself, ← hpreimage]
    change ‖(boundedSelfAdjointTransform (π b) - boundedSelfAdjointTransform S)
      (ξ i)‖ < ε
    refine (norm_boundedSelfAdjointTransform_sub_apply_le
      (hbself.map π) hS (ξ i)).trans_lt ?_
    have hl := hcoord (Sum.inl i)
    have hu := hcoord (Sum.inr i)
    have hs := add_lt_add hl hu
    simpa [η] using hs

/-- Closed-unit-ball self-adjoint Kaplansky density for an arbitrary unital
representation. No irreducibility or faithfulness is required. -/
theorem exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T) (hTnorm : ‖T‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε := by
  classical
  let M : ℝ := ∑ i : I, ‖T (ξ i)‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hξ (i : I) : ‖T (ξ i)‖ ≤ M :=
    Finset.single_le_sum (fun j _ => norm_nonneg (T (ξ j))) (Finset.mem_univ i)
  let d : ℝ := min (1 / 2) (ε / (2 * (M + 1)))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hε (by positivity))
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hde : d ≤ ε / (2 * (M + 1)) := min_le_right _ _
  have hbudget : d * M < ε / 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (M + 1))).mp hde
    nlinarith
  let r : ℝ := 1 - d
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let S : H →L[ℂ] H := (r : ℂ) • T
  have hSmem : S ∈ Set.centralizer (Set.centralizer (Set.range π)) := by
    exact (VonNeumannAlgebra.generated π.range).toStarSubalgebra.smul_mem hTmem (r : ℂ)
  have hS : IsSelfAdjoint S := by
    rw [isSelfAdjoint_iff]
    simp [S, star_smul, hT.star_eq]
  have hSnorm : ‖S‖ < 1 := by
    calc
      ‖S‖ = r * ‖T‖ := by
        simp [S, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hTnorm hr.le
      _ < 1 := by simpa using hr1
  obtain ⟨a, ha, hanorm, happ⟩ :=
    π.exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant_of_norm_lt_one
      ξ S hSmem hS hSnorm (half_pos hε)
  refine ⟨a, ha, hanorm, fun i => ?_⟩
  have htail : ‖S (ξ i) - T (ξ i)‖ < ε / 2 := by
    have heq : S (ξ i) - T (ξ i) = -(d : ℂ) • T (ξ i) := by
      change (r : ℂ) • T (ξ i) - T (ξ i) = -(d : ℂ) • T (ξ i)
      calc
        (r : ℂ) • T (ξ i) - T (ξ i) = ((r : ℂ) - 1) • T (ξ i) := by
          rw [sub_smul, one_smul]
        _ = -(d : ℂ) • T (ξ i) := by congr 1; simp [r]
    rw [heq, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    exact (mul_le_mul_of_nonneg_left (hξ i) hd.le).trans_lt hbudget
  calc
    ‖π a (ξ i) - T (ξ i)‖ ≤
        ‖π a (ξ i) - S (ξ i)‖ + ‖S (ξ i) - T (ξ i)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (happ i) htail
    _ = ε := add_halves ε

/-- The source norm can be bounded by the target norm in self-adjoint
finite-vector approximation throughout the represented bicommutant. -/
theorem exists_selfAdjoint_norm_le_forall_apply_sub_norm_lt_of_mem_bicommutant
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      ∀ i, ‖π a (ξ i) - T (ξ i)‖ < ε := by
  classical
  by_cases hzero : ‖T‖ = 0
  · have hz : T = 0 := norm_eq_zero.mp hzero
    subst T
    exact ⟨0, IsSelfAdjoint.zero A, by simp, fun i => by simpa using hε⟩
  have hpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hzero)
  let S : H →L[ℂ] H := ((‖T‖ : ℝ)⁻¹ : ℂ) • T
  have hSmem : S ∈ Set.centralizer (Set.centralizer (Set.range π)) :=
    (VonNeumannAlgebra.generated π.range).toStarSubalgebra.smul_mem hTmem _
  have hS : IsSelfAdjoint S := by
    rw [isSelfAdjoint_iff]
    simp [S, star_smul, hT.star_eq]
  have hSnorm : ‖S‖ ≤ 1 := by
    simp [S, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), hzero]
  obtain ⟨a, ha, hanorm, happ⟩ :=
    π.exists_selfAdjoint_norm_le_one_forall_apply_sub_norm_lt_of_mem_bicommutant
      ξ S hSmem hS hSnorm (div_pos hε hpos)
  refine ⟨(‖T‖ : ℂ) • a, ?_, ?_, fun i => ?_⟩
  · rw [isSelfAdjoint_iff]
    simp [star_smul, ha.star_eq]
  · calc
      ‖(‖T‖ : ℂ) • a‖ = ‖T‖ * ‖a‖ := by
        simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hanorm (norm_nonneg T)
      _ = ‖T‖ := mul_one _
  · have heq : π ((‖T‖ : ℂ) • a) (ξ i) - T (ξ i) =
        (‖T‖ : ℂ) • (π a (ξ i) - S (ξ i)) := by
      rw [map_smul]
      simp [S, smul_sub, smul_apply, smul_smul, hzero]
    rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hh := mul_lt_mul_of_pos_left (happ i) hpos
    have hcancel : ‖T‖ * (ε / ‖T‖) = ε := by
      rw [mul_comm ‖T‖ (ε / ‖T‖), div_mul_cancel₀ ε hzero]
    exact hh.trans_eq hcancel

/-- A self-adjoint bicommutant element is in the strong operator closure
of the represented source ball with the same norm budget. -/
theorem mem_sotClosure_image_closedBall_of_isSelfAdjoint
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
      closure ((fun a : A =>
        ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (π a)) ''
          Metric.closedBall (0 : A) ‖T‖) := by
  classical
  have hb := PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
    (σ := RingHom.id ℂ) (E := H) (F := H)
    (Metric.nhds_basis_ball (x := (0 : H)))
  apply (mem_closure_iff_nhds_basis
    (hb.nhds_of_zero
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T))).2
  rintro ⟨F, ε⟩ ⟨hF, hε⟩
  letI : Fintype F := @Fintype.ofFinite F hF
  obtain ⟨a, _, hanorm, ha⟩ :=
    π.exists_selfAdjoint_norm_le_forall_apply_sub_norm_lt_of_mem_bicommutant
      (fun x : F => (x : H)) T hTmem hT hε
  refine ⟨ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (π a),
    ⟨a, ?_, rfl⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hanorm
  · intro x hx
    change π a x - T x ∈ Metric.ball (0 : H) ε
    simpa only [Metric.mem_ball, dist_zero_right] using ha ⟨x, hx⟩

/-- The same bounded density in Mathlib's explicit WOT carrier. -/
theorem mem_wotClosure_image_closedBall_of_isSelfAdjoint
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hTmem : T ∈ Set.centralizer (Set.centralizer (Set.range π)))
    (hT : IsSelfAdjoint T) :
    ContinuousLinearMapWOT.ofCLM T ∈
      closure ((fun a : A => ContinuousLinearMapWOT.ofCLM (π a)) ''
        Metric.closedBall (0 : A) ‖T‖) := by
  have h := mem_closure_image
    (PointwiseConvergenceCLM.toWOT ℂ H H).continuous.continuousAt
    (π.mem_sotClosure_image_closedBall_of_isSelfAdjoint T hTmem hT)
  have heq (R : H →L[ℂ] H) : PointwiseConvergenceCLM.toWOT ℂ H H
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H R) =
      ContinuousLinearMapWOT.ofCLM R := rfl
  simpa only [Set.image_image, heq] using h

end StarAlgHom
