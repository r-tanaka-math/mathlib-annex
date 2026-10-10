/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-!
# Scalar regularity of complex ring equivalences

These scalar lemmas do not depend on biorthogonal sequences, the closed graph
 theorem, or geometric structure spaces. They are extracted without changing
 their proofs. The final RingEquiv dichotomy is an adapter-level result;
 `Complex.ringHom_eq_id_or_conj_of_continuous` already supplies the corresponding
 RingHom statement in the pinned Mathlib. No new scalar-classification claim
 or global upstream declaration audit is intended.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Complex

/-- Rational dilation makes a unit-ball bound on a ring map a continuity bound.
No continuity or measurability is assumed beforehand. -/
theorem continuous_ringEquiv_of_bounded_closedBall (σ : ℂ ≃+* ℂ)
    {C : ℝ} (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖σ z‖ ≤ C) : Continuous σ := by
  rw [Metric.continuous_iff]
  intro a ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hCn : C < ε * (n + 1) := by
    have hc : C < (n : ℝ) * ε := (div_lt_iff₀ hε).1 hn
    nlinarith
  refine ⟨1 / (n + 1 : ℝ), by positivity, ?_⟩
  intro b hb
  have hb' : ‖b - a‖ < 1 / (n + 1 : ℝ) := by simpa [dist_eq_norm] using hb
  have hz : ‖(n + 1 : ℂ) * (b - a)‖ ≤ 1 := by
    rw [norm_mul]
    have hnrm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by norm_cast
    rw [hnrm]
    simpa only [mul_comm] using ((lt_div_iff₀ hn0).1 hb').le
  have hbound := hC ((n + 1 : ℂ) * (b - a)) hz
  have hnrm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by norm_cast
  rw [map_mul, map_add, map_natCast, map_one, norm_mul, hnrm, map_sub] at hbound
  rw [dist_eq_norm]
  nlinarith

/-- Discontinuity forces arbitrarily large values already on the closed unit ball. -/
theorem exists_norm_map_gt_of_not_continuous (σ : ℂ ≃+* ℂ)
    (hσ : ¬ Continuous σ) (C : ℝ) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ C < ‖σ z‖ := by
  by_contra hn
  push_neg at hn
  exact hσ (continuous_ringEquiv_of_bounded_closedBall σ hn)

/-- The correct alternatives are `I` and `-I`, never `1` and `-1`. -/
theorem ringEquiv_apply_I_eq_or_eq_neg (σ : ℂ ≃+* ℂ) :
    σ I = I ∨ σ I = -I := by
  have hs : (σ I) ^ 2 = -1 := by
    rw [← map_pow, I_sq, map_neg, map_one]
  have hz : (σ I - I) * (σ I + I) = 0 := by
    calc
      (σ I - I) * (σ I + I) = (σ I) ^ 2 - I ^ 2 := by ring
      _ = 0 := by rw [hs, I_sq]; ring
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- Exact values on Gaussian rationals, for an arbitrary scalar automorphism. -/
theorem ringEquiv_apply_gaussian_rat (σ : ℂ ≃+* ℂ) (p q : ℚ) :
    σ ((p : ℂ) + (q : ℂ) * I) = (p : ℂ) + (q : ℂ) * σ I := by
  simp only [map_add, map_mul, map_ratCast]

/-- Rational density extends the real-axis part of the Gaussian-rational formula. -/
theorem ringEquiv_apply_ofReal_of_continuous (σ : ℂ ≃+* ℂ)
    (hσ : Continuous σ) (r : ℝ) : σ (r : ℂ) = r := by
  have h : (fun r : ℝ => σ (r : ℂ)) = fun r : ℝ => (r : ℂ) :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).equalizer
      (hσ.comp continuous_ofReal) continuous_ofReal (by
        funext q
        simpa only [Function.comp_apply, ofReal_ratCast, Rat.cast_zero, zero_mul, add_zero]
          using ringEquiv_apply_gaussian_rat σ q 0)
  exact congrFun h r

/-- Continuity plus the Gaussian-rational identities classifies the actual
RingEquiv. The two real coordinates are extended before evaluating a complex point. -/
theorem ringEquiv_eq_refl_or_conj_of_continuous (σ : ℂ ≃+* ℂ)
    (hσ : Continuous σ) :
    σ = RingEquiv.refl ℂ ∨ σ = starRingAut (R := ℂ) := by
  have hr := ringEquiv_apply_ofReal_of_continuous σ hσ
  rcases ringEquiv_apply_I_eq_or_eq_neg σ with hi | hi
  · left
    apply RingEquiv.ext
    intro z
    calc
      σ z = σ ((z.re : ℂ) + (z.im : ℂ) * I) := by rw [re_add_im]
      _ = z := by rw [map_add, map_mul, hr, hr, hi, re_add_im]
  · right
    apply RingEquiv.ext
    intro z
    change σ z = conj z
    calc
      σ z = σ ((z.re : ℂ) + (z.im : ℂ) * I) := by rw [re_add_im]
      _ = conj z := by
        rw [map_add, map_mul, hr, hr, hi]
        apply Complex.ext <;> simp

end Complex
