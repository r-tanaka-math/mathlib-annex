import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Analytic.DyadicCFC

/-!
# Exact signed dyadic decomposition with a uniform state cost

The cutoff index is selected by an elementary Archimedean estimate; no
infinite spectral measure or limit of algebra elements is required.
SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear.Analytic

open MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]

/-- Dyadic levels are cofinal for every strictly positive initial cutoff. -/
theorem exists_dyadicLevel_ge {T : ℝ} (hT : 0 < T) (K : ℝ) :
    ∃ N : ℕ, K ≤ dyadicLevel T N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (K / T)
  have hpow : ∀ n : ℕ, (n : ℝ) + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Nat.cast_succ, pow_succ]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨N, ?_⟩
  have hKT : K ≤ (N : ℝ) * T := (div_le_iff₀ hT).mp hN
  have hNT : (N : ℝ) * T ≤ 2 ^ N * T := by
    apply mul_le_mul_of_nonneg_right _ hT.le
    linarith [hpow N]
  exact hKT.trans hNT

/-- The negative truncated part is evaluated in the same real CFC as the
positive part.  This is a composition identity, not an Arens extension. -/
theorem cfc_truncate_neg (L : ℝ) (a : A) (ha : IsSelfAdjoint a) :
    cfc (truncatePos L) (-a) = cfc (fun x : ℝ ↦ truncatePos L (-x)) a := by
  have hn : cfc (fun x : ℝ ↦ -x) a = -a := by
    rw [cfc_neg, cfc_id' ℝ a ha]
  have hc := cfc_comp (truncatePos L) (fun x : ℝ ↦ -x) a ha
    (continuous_truncatePos L).continuousOn (by fun_prop)
  rw [hn] at hc
  exact hc.symm

/-- Reconstruction from positive and negative continuous truncations at a
large enough cutoff. -/
theorem cfc_signed_truncate_eq (L : ℝ) (a : A) (ha : IsSelfAdjoint a)
    (hL : ‖a‖ ≤ L) :
    cfc (truncatePos L) a - cfc (truncatePos L) (-a) = a := by
  rw [cfc_truncate_neg L a ha]
  rw [← cfc_sub (truncatePos L) (fun x : ℝ ↦ truncatePos L (-x)) a
    (continuous_truncatePos L).continuousOn
    (((continuous_truncatePos L).comp continuous_neg).continuousOn)]
  have hc : cfc (fun x : ℝ ↦ truncatePos L x - truncatePos L (-x)) a =
      cfc (fun x : ℝ ↦ x) a := by
    apply cfc_congr
    intro x hx
    apply signed_truncate_eq
    have hnorm : ‖x‖ ≤ ‖a‖ := spectrum.norm_le_norm_of_mem hx
    simpa only [Real.norm_eq_abs] using hnorm.trans hL
  rw [hc, cfc_id' ℝ a ha]

def signedSlices (T : ℝ) (a : A) (N : ℕ) : List (ℝ × A) :=
  positiveSlices T a N ++ negateCoefficients (positiveSlices T (-a) N)

theorem hasEffects_signedSlices {T : ℝ} (hT : 0 < T) (a : A) (N : ℕ) :
    HasEffects (signedSlices T a N) := by
  intro cp hcp
  rcases List.mem_append.mp hcp with hp | hn
  · exact hasEffects_positiveSlices hT a N cp hp
  · exact hasEffects_negateCoefficients (hasEffects_positiveSlices hT (-a) N) cp hn

theorem signedSlices_value {T : ℝ} (hT : 0 < T) (a : A) (ha : IsSelfAdjoint a)
    (N : ℕ) (hN : ‖a‖ ≤ dyadicLevel T N) :
    effectValue (signedSlices T a N) = a := by
  rw [signedSlices, effectValue_append, effectValue_negateCoefficients,
    positiveSlices_value hT, positiveSlices_value hT, ← sub_eq_add_neg]
  exact cfc_signed_truncate_eq _ a ha hN

/-- The total signed cost is bounded without any dependence on the number
of slices or the ambient dimension. -/
theorem signedSlices_cost_le (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    {T : ℝ} (hT : 0 < T) (a : A) (ha : IsSelfAdjoint a) (N : ℕ) :
    effectCost phi (signedSlices T a N) ≤
      2 * T + 4 * Real.sqrt (fourthMoment phi a) / T := by
  rw [signedSlices, effectCost_append, effectCost_negateCoefficients]
  have hp := positiveSlices_cost_le phi hphi hT a ha N
  have hn := positiveSlices_cost_le phi hphi hT (-a) ha.neg N
  rw [fourthMoment_neg] at hn
  calc
    _ ≤ (T + 2 * Real.sqrt (fourthMoment phi a) / T) +
        (T + 2 * Real.sqrt (fourthMoment phi a) / T) := add_le_add hp hn
    _ = _ := by ring

/-- A constructed signed effect decomposition for every positive cutoff.
The effect list is not supplied as an extra structural hypothesis. -/
theorem exists_signed_effect_decomposition
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (a : A) (ha : IsSelfAdjoint a) {T : ℝ} (hT : 0 < T) :
    ∃ L : List (ℝ × A), HasEffects L ∧ effectValue L = a ∧
      effectCost phi L ≤ 2 * T + 4 * Real.sqrt (fourthMoment phi a) / T := by
  obtain ⟨N, hN⟩ := exists_dyadicLevel_ge hT ‖a‖
  exact ⟨signedSlices T a N, hasEffects_signedSlices hT a N,
    signedSlices_value hT a ha N hN, signedSlices_cost_le phi hphi hT a ha N⟩

end MathlibAnnex.CStarBilinear.Analytic
