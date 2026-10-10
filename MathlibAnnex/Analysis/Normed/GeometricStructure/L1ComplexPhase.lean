/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1Kernel
import MathlibAnnex.Analysis.Normed.Module.DualKernelPair
import Mathlib.Analysis.Complex.Norm
import MathlibAnnex.Analysis.Complex.UnitPhase
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Complex phase ratios for coefficient kernels on ℓ¹

The pairing is the existing bilinear coefficient pairing, so the relevant ratio
is `u n * conj (v n)`. The imported `Complex.UnitPhase` lemmas subtract the
values of a quadratic polynomial at three distinct points. This repairs the
incorrect implication from equality of real parts to equality of phases in the
source text. No restriction to a range of exactly three points is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate
open scoped lp ENNReal


namespace NormedSpace

/-- The relative phase of two bounded complex coefficient sequences. -/
def l1PhaseRatio (u v : ℓ^∞(ℕ, ℂ)) (n : ℕ) : ℂ := u n * conj (v n)


theorem l1PhaseRatio_mul_right (u v : ℓ^∞(ℕ, ℂ)) (hv : ∀ n, ‖v n‖ = 1) (n : ℕ) :
    l1PhaseRatio u v n * v n = u n := by
  change (u n * conj (v n)) * v n = u n
  calc
    (u n * conj (v n)) * v n = u n * (v n * conj (v n)) := by ring
    _ = u n := by rw [Complex.mul_conj_eq_one_of_norm_eq_one (hv n), mul_one]

theorem norm_l1PhaseRatio (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) (n : ℕ) :
    ‖l1PhaseRatio u v n‖ = 1 := by
  simp only [l1PhaseRatio, norm_mul, Complex.norm_conj, hu, hv, mul_one]

@[simp]
theorem l1PhaseRatio_self (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    l1PhaseRatio u u n = 1 :=
  Complex.mul_conj_eq_one_of_norm_eq_one (hu n)

/-- Reversing the ratio conjugates its value. -/
theorem l1PhaseRatio_swap (u v : ℓ^∞(ℕ, ℂ)) (n : ℕ) :
    l1PhaseRatio v u n = conj (l1PhaseRatio u v n) := by
  simp only [l1PhaseRatio, map_mul, Complex.conj_conj, mul_comm]

/-- The pointwise cocycle identity uses unimodularity only of the middle sequence. -/
theorem l1PhaseRatio_mul (u v w : ℓ^∞(ℕ, ℂ)) (hv : ∀ n, ‖v n‖ = 1) (n : ℕ) :
    l1PhaseRatio u v n * l1PhaseRatio v w n = l1PhaseRatio u w n := by
  change (u n * conj (v n)) * (v n * conj (w n)) = u n * conj (w n)
  calc
    (u n * conj (v n)) * (v n * conj (w n)) =
        (v n * conj (v n)) * (u n * conj (w n)) := by ring
    _ = u n * conj (w n) := by
      rw [Complex.mul_conj_eq_one_of_norm_eq_one (hv n), one_mul]

/-- The actual point of the original, maximal-face-defined geometric structure space. -/
def l1ComplexKernelPoint (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1) :
    GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ) :=
  ⟨(lp.coefficientFunctional u : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0},
    preimage_zero_coefficientFunctional_mem_geometricStructureFamily ℂ u hu⟩

@[simp]
theorem mem_l1ComplexKernelPoint (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1)
    (a : ℓ¹(ℕ, ℂ)) :
    a ∈ (l1ComplexKernelPoint u hu).val ↔ lp.coefficientFunctional u a = 0 := Iff.rfl

/-- Every actual GSS point has a unimodular coefficient representative. -/
theorem exists_l1ComplexKernelPoint_eq (I : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ)) :
    ∃ (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ n, ‖u n‖ = 1), l1ComplexKernelPoint u hu = I := by
  obtain ⟨u, hu, hI⟩ := (mem_geometricStructureFamily_l1_iff ℂ I.val).1 I.property
  exact ⟨u, hu, Subtype.ext hI⟩

/-- A constant relative phase is exactly equality of the actual kernel points. -/
theorem l1ComplexKernelPoint_eq_iff_exists_const_ratio (u v : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) (hv : ∀ n, ‖v n‖ = 1) :
    l1ComplexKernelPoint u hu = l1ComplexKernelPoint v hv ↔
      ∃ c : ℂ, ∀ n, l1PhaseRatio u v n = c := by
  have hvne : lp.coefficientFunctional v ≠ 0 := norm_ne_zero_iff.1 (by
    rw [lp.norm_coefficientFunctional_eq_one_of_forall_norm_eq_one v hv]
    exact one_ne_zero)
  constructor
  · intro h
    have hker : (lp.coefficientFunctional v).ker = (lp.coefficientFunctional u).ker := by
      apply SetLike.coe_injective
      exact (congrArg Subtype.val h).symm
    obtain ⟨c, _, hc⟩ := (ContinuousLinearMap.ker_eq_ker_iff_exists_ne_zero_smul hvne).1 hker
    refine ⟨c, fun n => ?_⟩
    have hval := congrArg (fun f : StrongDual ℂ ℓ¹(ℕ, ℂ) => f (lp.single 1 n 1)) hc
    have hval' : u n = c * v n := by
      simpa only [lp.coefficientFunctional_single, one_mul,
        ContinuousLinearMap.smul_apply, smul_eq_mul] using hval
    change u n * conj (v n) = c
    rw [hval', mul_assoc, Complex.mul_conj_eq_one_of_norm_eq_one (hv n), mul_one]
  · rintro ⟨c, hc⟩
    have hcnorm : ‖c‖ = 1 := by
      rw [← hc 0]
      exact norm_l1PhaseRatio u v hu hv 0
    have hcne : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hcnorm]; exact one_ne_zero)
    have huv : u = c • v := by
      apply Subtype.ext
      funext n
      change u n = c * v n
      rw [← hc n]
      exact (l1PhaseRatio_mul_right u v hv n).symm
    apply Subtype.ext
    change (lp.coefficientFunctional u : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0} =
      (lp.coefficientFunctional v : ℓ¹(ℕ, ℂ) → ℂ) ⁻¹' {0}
    rw [huv]
    exact lp.preimage_zero_coefficientFunctional_smul v hcne

end NormedSpace

