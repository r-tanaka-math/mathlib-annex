/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Elementary geometry of complex unit phases

Conjugate cancellation, three-point affine rigidity on the unit circle,
and an explicit phase avoiding two prescribed values.
These scalar lemmas do not depend on sequence spaces or geometric structure spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate

namespace Complex

/-- Unit norm implies the conjugate cancellation needed below. -/
theorem mul_conj_eq_one_of_norm_eq_one {r : ℂ} (hr : ‖r‖ = 1) :
    r * conj r = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hr, one_pow, Complex.ofReal_one]


end Complex

namespace Complex

/-- An affine map taking three distinct unit phases to unit phases has zero
mixed coefficient. This is the circle/line intersection argument expressed
by a quadratic polynomial; equality of real parts alone is never cancelled. -/
theorem mul_conj_eq_zero_of_norm_affine_eq_one_three
    (a b r s t : ℂ) (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (har : ‖a * r + b‖ = 1) (has : ‖a * s + b‖ = 1) (hat : ‖a * t + b‖ = 1) :
    a * conj b = 0 := by
  let A : ℂ := a * conj b
  let B : ℂ := a * conj a + b * conj b - 1
  let C : ℂ := b * conj a
  have hp (z : ℂ) (hz : ‖z‖ = 1) (haz : ‖a * z + b‖ = 1) :
      A * z ^ 2 + B * z + C = 0 := by
    have hzz := Complex.mul_conj_eq_one_of_norm_eq_one hz
    have haz' : (a * z + b) * (conj a * conj z + conj b) = 1 := by
      simpa only [map_add, map_mul] using Complex.mul_conj_eq_one_of_norm_eq_one haz
    calc
      A * z ^ 2 + B * z + C =
          ((a * z + b) * (conj a * conj z + conj b) - 1) * z +
            (1 - z * conj z) * (a * conj a * z + b * conj a) := by
        dsimp only [A, B, C]
        ring
      _ = 0 := by rw [haz', hzz]; ring
  have hdiff (z w : ℂ) (hzw : z ≠ w)
      (hz : A * z ^ 2 + B * z + C = 0) (hw : A * w ^ 2 + B * w + C = 0) :
      A * (z + w) + B = 0 := by
    have hprod : (z - w) * (A * (z + w) + B) = 0 := by
      calc
        (z - w) * (A * (z + w) + B) =
            (A * z ^ 2 + B * z + C) - (A * w ^ 2 + B * w + C) := by ring
        _ = 0 := by rw [hz, hw]; ring
    exact (mul_eq_zero.1 hprod).resolve_left (sub_ne_zero.2 hzw)
  have hrs' := hdiff r s hrs (hp r hr har) (hp s hs has)
  have hrt' := hdiff r t hrt (hp r hr har) (hp t ht hat)
  have hA : A * (s - t) = 0 := by
    calc
      A * (s - t) = (A * (r + s) + B) - (A * (r + t) + B) := by ring
      _ = 0 := by rw [hrs', hrt']; ring
  exact (mul_eq_zero.1 hA).resolve_right (sub_ne_zero.2 hst)

/-- The preceding conclusion in the form needed for functional kernels. -/
theorem eq_zero_or_eq_zero_of_norm_affine_eq_one_three
    (a b r s t : ℂ) (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (har : ‖a * r + b‖ = 1) (has : ‖a * s + b‖ = 1) (hat : ‖a * t + b‖ = 1) :
    a = 0 ∨ b = 0 := by
  rcases mul_eq_zero.1 (mul_conj_eq_zero_of_norm_affine_eq_one_three
    a b r s t hr hs ht hrs hrt hst har has hat) with ha | hb
  · exact Or.inl ha
  · right
    have h := congrArg conj hb
    simpa only [Complex.conj_conj, map_zero] using h

/-- Choose a new phase avoiding both old projective coefficient classes.
Only the two explicit phases `-1` and `I` are needed. -/
theorem exists_unit_phase_mul_ne (r s : ℂ) (hs : s ≠ 0) :
    ∃ t : ℂ, ‖t‖ = 1 ∧ t ≠ 1 ∧ t * s ≠ r := by
  have hI1 : Complex.I ≠ (1 : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hIm1 : Complex.I ≠ (-1 : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  by_cases h : (-1 : ℂ) * s = r
  · refine ⟨Complex.I, Complex.norm_I, hI1, ?_⟩
    intro ht
    exact hIm1 (mul_right_cancel₀ hs (ht.trans h.symm))
  · exact ⟨(-1 : ℂ), by norm_num [Complex.norm_def], by norm_num, h⟩

end Complex
