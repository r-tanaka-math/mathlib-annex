/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.Normed.GeometricStructure.L1ComplexRelated
import MathlibAnnex.Analysis.Normed.GeometricStructure.Spectrum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Intersections of complex ℓ¹ components

Negating a single coefficient stays in the same actual GSS component. The
pairing is the existing bilinear series `∑' n, a n * u n`. Absolute summability
justifies subtracting the two series; the difference has single-point support.
The intersection is a set in ℓ¹, not a submodule supplied by an extra hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set ComplexConjugate
open scoped lp ENNReal

namespace NormedSpace

/-- Negate one coordinate of an actual bounded unimodular coefficient sequence. -/
def l1PhaseFlip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1) (n : ℕ) : ℓ^∞(ℕ, ℂ) :=
  lp.inftyOfNormOne (fun m => if m = n then -u m else u m)
    (fun m => by split_ifs <;> simp only [norm_neg, hu])

@[simp]
theorem l1PhaseFlip_apply (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1) (n m : ℕ) :
    l1PhaseFlip u hu n m = if m = n then -u m else u m := rfl

@[simp]
theorem norm_l1PhaseFlip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1) (n m : ℕ) :
    ‖l1PhaseFlip u hu n m‖ = 1 := by
  rw [l1PhaseFlip_apply]
  split_ifs <;> simp only [norm_neg, hu]

/-- The relative phase is minus one at the flipped coordinate and one elsewhere. -/
theorem l1PhaseRatio_flip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1) (n m : ℕ) :
    l1PhaseRatio u (l1PhaseFlip u hu n) m = if m = n then -1 else 1 := by
  change u m * conj (if m = n then -u m else u m) = _
  split_ifs <;> simp only [map_neg, mul_neg, Complex.mul_conj_eq_one_of_norm_eq_one (hu m)]

/-- The actual kernel of a single-coordinate flip belongs to the same component. -/
theorem related_l1ComplexKernelPoint_flip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1)
    (n : ℕ) :
    (geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).Related (l1ComplexKernelPoint u hu)
      (l1ComplexKernelPoint (l1PhaseFlip u hu n) (norm_l1PhaseFlip u hu n)) := by
  apply (related_l1ComplexKernelPoint_iff _ _ hu (norm_l1PhaseFlip u hu n)).2
  apply ((Set.finite_singleton (1 : ℂ)).insert (-1)).subset
  rintro _ ⟨m, rfl⟩
  rw [l1PhaseRatio_flip]
  split_ifs <;> simp

/-- Subtracting the two absolutely convergent series leaves a single summand. -/
theorem tsum_sub_mul_l1PhaseFlip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1)
    (n : ℕ) (a : ℓ¹(ℕ, ℂ)) :
    (∑' m, a m * u m) - (∑' m, a m * l1PhaseFlip u hu n m) = 2 * a n * u n := by
  rw [← (lp.summable_mul_coefficients a u).tsum_sub
    (lp.summable_mul_coefficients a (l1PhaseFlip u hu n)), tsum_eq_single n]
  · simp [l1PhaseFlip_apply] <;> ring
  · intro m hmn
    simp only [l1PhaseFlip_apply, if_neg hmn, sub_self]

/-- The exact pairing difference, with no conjugation inserted into the coefficients. -/
theorem coefficientFunctional_sub_l1PhaseFlip (u : ℓ^∞(ℕ, ℂ))
    (hu : ∀ m, ‖u m‖ = 1) (n : ℕ) (a : ℓ¹(ℕ, ℂ)) :
    lp.coefficientFunctional u a - lp.coefficientFunctional (l1PhaseFlip u hu n) a =
      2 * a n * u n :=
  tsum_sub_mul_l1PhaseFlip u hu n a

/-- The series with one term changed, expressed using the original series. -/
theorem tsum_mul_l1PhaseFlip (u : ℓ^∞(ℕ, ℂ)) (hu : ∀ m, ‖u m‖ = 1)
    (n : ℕ) (a : ℓ¹(ℕ, ℂ)) :
    (∑' m, a m * l1PhaseFlip u hu n m) = (∑' m, a m * u m) - 2 * a n * u n := by
  calc
    (∑' m, a m * l1PhaseFlip u hu n m) =
        (∑' m, a m * u m) -
          ((∑' m, a m * u m) - (∑' m, a m * l1PhaseFlip u hu n m)) := by ring
    _ = (∑' m, a m * u m) - 2 * a n * u n := by
      rw [tsum_sub_mul_l1PhaseFlip u hu n a]

/-- The common intersection of every member of an actual complex ℓ¹ component is zero. -/
theorem kernel_component_l1ComplexKernelPoint (u : ℓ^∞(ℕ, ℂ))
    (hu : ∀ n, ‖u n‖ = 1) :
    ClosureSpace.HullKernel.kernel (geometricStructureFamily ℂ ℓ¹(ℕ, ℂ))
      ((geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).component (l1ComplexKernelPoint u hu)) = {0} := by
  apply Set.ext
  intro a
  constructor
  · intro ha
    have hbase : lp.coefficientFunctional u a = 0 :=
      ha (l1ComplexKernelPoint u hu)
        ((geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).mem_component (l1ComplexKernelPoint u hu))
    apply Set.mem_singleton_iff.2
    apply Subtype.ext
    funext n
    have hflip : lp.coefficientFunctional (l1PhaseFlip u hu n) a = 0 :=
      ha (l1ComplexKernelPoint (l1PhaseFlip u hu n) (norm_l1PhaseFlip u hu n))
        (related_l1ComplexKernelPoint_flip u hu n)
    have hdiff := coefficientFunctional_sub_l1PhaseFlip u hu n a
    rw [hbase, hflip, sub_self] at hdiff
    have hun : u n ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
    have hzero : a n = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 hdiff.symm).resolve_right hun)).resolve_left
        (by norm_num : (2 : ℂ) ≠ 0)
    exact hzero
  · rintro rfl J _
    obtain ⟨v, hv, rfl⟩ := exists_l1ComplexKernelPoint_eq J
    change lp.coefficientFunctional v 0 = 0
    exact map_zero _

/-- The same intersection formula with an arbitrary actual GSS seed. -/
theorem kernel_component_geometricStructureClosure_l1Complex
    (I : GeometricStructureSpace ℂ ℓ¹(ℕ, ℂ)) :
    ClosureSpace.HullKernel.kernel (geometricStructureFamily ℂ ℓ¹(ℕ, ℂ))
      ((geometricStructureClosure ℂ ℓ¹(ℕ, ℂ)).component I) = {0} := by
  obtain ⟨u, hu, rfl⟩ := exists_l1ComplexKernelPoint_eq I
  exact kernel_component_l1ComplexKernelPoint u hu

/-- Every geometric-spectrum point has the same zero intersection, without identifying
its component carrier with any other component. -/
theorem geometricSpectrumKernel_l1Complex (C : GeometricSpectrum ℂ ℓ¹(ℕ, ℂ)) :
    geometricSpectrumKernel ℂ ℓ¹(ℕ, ℂ) C = {0} := by
  obtain ⟨I, rfl⟩ := toGeometricSpectrum_surjective ℂ ℓ¹(ℕ, ℂ) C
  exact kernel_component_geometricStructureClosure_l1Complex I

end NormedSpace
