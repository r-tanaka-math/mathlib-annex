import MathlibAnnex.Analysis.CStarAlgebra.PureStateHomogeneity.KishimotoOzawaSakai

/-!
# Convex purity and dominated positive functionals

This is the elementary convex-cone part of the pure-state/GNS bridge.  It is
kept separate from the Hilbert-space Riesz argument.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder Convex

namespace MathlibAnnex.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A positive continuous functional on a unital C-star algebra which
vanishes at one is the zero functional. -/
theorem continuousLinearMap_eq_zero_of_nonnegative_of_one_eq_zero
    (rho : A →L[ℂ] ℂ) (hrho : ∀ a : A, 0 ≤ a → 0 ≤ rho a)
    (hrho_one : rho 1 = 0) : rho = 0 := by
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ rho.toLinearMap hrho
  have hf_one : f 1 = 0 := hrho_one
  have hf_zero_of_nonneg (a : A) (ha : 0 ≤ a) : f a = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa [hf_one] using f.norm_apply_le_of_nonneg a ha
    · exact norm_nonneg _
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨x, hx_nonneg, -, ha⟩ := CStarAlgebra.exists_sum_four_nonneg a
  change f a = 0
  rw [ha, map_sum]
  simp [hf_zero_of_nonneg, hx_nonneg]

/-- Cone characterization in the direction needed by a reducing projection:
a positive functional dominated by a pure state is a real scalar multiple of
that state. -/
theorem eq_smul_of_pureState_of_nonnegative_le
    (phi rho : A →L[ℂ] ℂ) (hphi : IsPureState A phi)
    (hrho : ∀ a : A, 0 ≤ a → 0 ≤ rho a)
    (hle : ∀ a : A, 0 ≤ a → rho a ≤ phi a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ rho = t • phi := by
  rw [IsPureState, mem_extremePoints_iff_left] at hphi
  obtain ⟨t, ht, ht_eq⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (hrho 1 (by simpa using star_mul_self_nonneg (1 : A)))
  have ht_le_one : t ≤ 1 := by
    have h := hle 1 (by simpa using star_mul_self_nonneg (1 : A))
    rw [hphi.1.2] at h
    have hre := (RCLike.nonneg_iff.mp (sub_nonneg.mpr h)).1
    have ht_re : (rho 1).re = t := by
      simpa using congrArg Complex.re ht_eq.symm
    simpa [ht_re] using hre
  by_cases ht_zero : t = 0
  · refine ⟨t, ht, ht_le_one, ?_⟩
    have hrho_one : rho 1 = 0 := by simpa [ht_zero] using ht_eq.symm
    rw [continuousLinearMap_eq_zero_of_nonnegative_of_one_eq_zero rho hrho hrho_one,
      ht_zero]
    exact (zero_smul ℝ phi).symm
  by_cases ht_one : t = 1
  · refine ⟨t, ht, ht_le_one, ?_⟩
    have hdiff_nonneg : ∀ a : A, 0 ≤ a → 0 ≤ (phi - rho) a := by
      intro a ha
      simpa using sub_nonneg.mpr (hle a ha)
    have hdiff_one : (phi - rho) 1 = 0 := by
      simp [hphi.1.2, ← ht_eq, ht_one]
    have hdiff := continuousLinearMap_eq_zero_of_nonnegative_of_one_eq_zero
      (phi - rho) hdiff_nonneg hdiff_one
    rw [ht_one, one_smul]
    exact (sub_eq_zero.mp hdiff).symm
  have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
  have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht_pos.ne'
  have hsubC : (1 - (t : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm ht_one)
  let psi : A →L[ℂ] ℂ := t⁻¹ • rho
  let chi : A →L[ℂ] ℂ := (1 - t)⁻¹ • (phi - rho)
  have hpsi : psi ∈ stateSpace A := by
    constructor
    · intro a ha
      dsimp [psi]
      exact smul_nonneg (inv_nonneg.mpr ht.le) (hrho a ha)
    · dsimp [psi]
      rw [ContinuousLinearMap.smul_apply, ← ht_eq]
      simpa [ht_pos.ne']
  have hchi : chi ∈ stateSpace A := by
    constructor
    · intro a ha
      dsimp [chi]
      exact smul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr ht_le_one))
        (sub_nonneg.mpr (hle a ha))
    · dsimp [chi]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        hphi.1.2, ← ht_eq]
      rw [Complex.real_smul]
      push_cast
      exact inv_mul_cancel₀ hsubC
  have hsegment : phi ∈ openSegment ℝ psi chi := by
    refine ⟨t, 1 - t, ht_pos, sub_pos.mpr ht_lt_one, by ring, ?_⟩
    apply ContinuousLinearMap.ext
    intro a
    dsimp [psi, chi]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply]
    simp only [Complex.real_smul]
    push_cast
    simp [htC, hsubC]
  have hpsi_eq : psi = phi := hphi.2 psi hpsi chi hchi hsegment
  refine ⟨t, ht, ht_le_one, ?_⟩
  calc
    rho = t • psi := by
      apply ContinuousLinearMap.ext
      intro a
      dsimp [psi]
      simp [ht_pos.ne']
    _ = t • phi := congrArg (t • ·) hpsi_eq

end MathlibAnnex.CStarAlgebra
