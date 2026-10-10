/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic

/-!
# Left unitary translation of functionals on a nonunital C-star algebra

The unitary belongs to the canonical unitization. Its left multiplication
preserves the original algebra and its norm. Translation is precomposition,
so its multiplication order is reversed. No positive decomposition or
existence of a translating unitary is assumed or asserted in this file.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Left multiplication by a unitization element, with values in the original algebra. -/
def unitizationLeftMul (z : Unitization ℂ A) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := fun a => z.fst • a + z.snd * a
      map_add' := by intros; simp [smul_add, mul_add]; abel
      map_smul' := by intros; simp [smul_add, mul_smul_comm, smul_smul, mul_comm] }
    (‖z.fst‖ + ‖z.snd‖) fun a => by
      calc
        ‖z.fst • a + z.snd * a‖ ≤ ‖z.fst • a‖ + ‖z.snd * a‖ := norm_add_le _ _
        _ ≤ ‖z.fst‖ * ‖a‖ + ‖z.snd‖ * ‖a‖ := by
          rw [norm_smul]
          exact add_le_add le_rfl (norm_mul_le z.snd a)
        _ = (‖z.fst‖ + ‖z.snd‖) * ‖a‖ := by ring

@[simp]
theorem unitizationLeftMul_apply (z : Unitization ℂ A) (a : A) :
    unitizationLeftMul z a = z.fst • a + z.snd * a := rfl

/-- The value is the product in the unitization, not a formal new unit in `A`. -/
theorem inr_unitizationLeftMul (z : Unitization ℂ A) (a : A) :
    (unitizationLeftMul z a : Unitization ℂ A) = z * (a : Unitization ℂ A) := by
  induction z using Unitization.ind with
  | inl_add_inr c b =>
    simp [unitizationLeftMul_apply, add_mul, Unitization.inl_mul_inr,
      Unitization.inr_mul]

@[simp]
theorem unitizationLeftMul_one (a : A) :
    unitizationLeftMul (1 : Unitization ℂ A) a = a := by simp

/-- Composition agrees with multiplication in the unitization. -/
theorem unitizationLeftMul_mul (z w : Unitization ℂ A) (a : A) :
    unitizationLeftMul (z * w) a = unitizationLeftMul z (unitizationLeftMul w a) := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [inr_unitizationLeftMul, mul_assoc]

/-- Left multiplication by a unitary is isometric on the original algebra. -/
theorem norm_unitizationLeftMul_unitary (u : unitary (Unitization ℂ A)) (a : A) :
    ‖unitizationLeftMul (u : Unitization ℂ A) a‖ = ‖a‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ), inr_unitizationLeftMul,
    CStarRing.norm_coe_unitary_mul, Unitization.norm_inr]

/-- The notes' notation `rho u` means `a ↦ rho (u * a)`, not an adjoint. -/
def unitaryTranslate (u : unitary (Unitization ℂ A))
    (rho : StrongDual ℂ A) : StrongDual ℂ A :=
  rho.comp (unitizationLeftMul (u : Unitization ℂ A))

@[simp]
theorem unitaryTranslate_apply (u : unitary (Unitization ℂ A))
    (rho : StrongDual ℂ A) (a : A) :
    unitaryTranslate u rho a = rho (unitizationLeftMul (u : Unitization ℂ A) a) := rfl

@[simp]
theorem unitaryTranslate_one (rho : StrongDual ℂ A) : unitaryTranslate 1 rho = rho := by
  ext a
  simp

/-- Precomposition reverses the multiplication order. -/
theorem unitaryTranslate_mul (u v : unitary (Unitization ℂ A))
    (rho : StrongDual ℂ A) :
    unitaryTranslate (u * v) rho = unitaryTranslate v (unitaryTranslate u rho) := by
  ext a
  simp only [unitaryTranslate_apply, Submonoid.coe_mul, unitizationLeftMul_mul]

@[simp]
theorem unitaryTranslate_star_translate (u : unitary (Unitization ℂ A))
    (rho : StrongDual ℂ A) :
    unitaryTranslate (star u) (unitaryTranslate u rho) = rho := by
  rw [← unitaryTranslate_mul, Unitary.mul_star_self, unitaryTranslate_one]

@[simp]
theorem unitaryTranslate_translate_star (u : unitary (Unitization ℂ A))
    (rho : StrongDual ℂ A) :
    unitaryTranslate u (unitaryTranslate (star u) rho) = rho := by
  rw [← unitaryTranslate_mul, Unitary.star_mul_self, unitaryTranslate_one]

theorem unitaryTranslate_injective (u : unitary (Unitization ℂ A)) :
    Function.Injective (unitaryTranslate u : StrongDual ℂ A → StrongDual ℂ A) := by
  intro rho sigma h
  simpa using congrArg (unitaryTranslate (star u)) h

@[simp]
theorem unitaryTranslate_add (u : unitary (Unitization ℂ A))
    (rho sigma : StrongDual ℂ A) :
    unitaryTranslate u (rho + sigma) = unitaryTranslate u rho + unitaryTranslate u sigma := by
  ext a
  rfl

@[simp]
theorem unitaryTranslate_real_smul (u : unitary (Unitization ℂ A))
    (t : ℝ) (rho : StrongDual ℂ A) :
    unitaryTranslate u (t • rho) = t • unitaryTranslate u rho := by
  ext a
  rfl

/-- Both norm inequalities are proved, using translation by the inverse unitary. -/
theorem norm_unitaryTranslate (u : unitary (Unitization ℂ A)) (rho : StrongDual ℂ A) :
    ‖unitaryTranslate u rho‖ = ‖rho‖ := by
  have bound (v : unitary (Unitization ℂ A)) (f : StrongDual ℂ A) :
      ‖unitaryTranslate v f‖ ≤ ‖f‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro a
    simpa only [unitaryTranslate_apply, norm_unitizationLeftMul_unitary] using
      f.le_opNorm (unitizationLeftMul (v : Unitization ℂ A) a)
  apply le_antisymm (bound u rho)
  simpa only [unitaryTranslate_star_translate] using bound (star u) (unitaryTranslate u rho)

/-- Unitary translation preserves extremality in the entire dual ball.
No positivity or decomposition hypothesis occurs here. -/
theorem unitaryTranslate_mem_extremePoints_closedBall
    (u : unitary (Unitization ℂ A)) {rho : StrongDual ℂ A}
    (hrho : rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ) :
    unitaryTranslate u rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left] at hrho ⊢
  refine ⟨?_, ?_⟩
  · simpa only [mem_closedBall_zero_iff, norm_unitaryTranslate] using hrho.1
  · intro f hf g hg hsegment
    have hf' : unitaryTranslate (star u) f ∈ closedBall (0 : StrongDual ℂ A) 1 := by
      simpa only [mem_closedBall_zero_iff, norm_unitaryTranslate] using hf
    have hg' : unitaryTranslate (star u) g ∈ closedBall (0 : StrongDual ℂ A) 1 := by
      simpa only [mem_closedBall_zero_iff, norm_unitaryTranslate] using hg
    obtain ⟨s, t, hs, ht, hst, hcomb⟩ := hsegment
    have hcomb' : s • unitaryTranslate (star u) f + t • unitaryTranslate (star u) g = rho := by
      simpa only [unitaryTranslate_add, unitaryTranslate_real_smul,
        unitaryTranslate_star_translate] using congrArg (unitaryTranslate (star u)) hcomb
    have heq := hrho.2 (unitaryTranslate (star u) f) hf'
      (unitaryTranslate (star u) g) hg' ⟨s, t, hs, ht, hst, hcomb'⟩
    simpa only [unitaryTranslate_translate_star] using congrArg (unitaryTranslate u) heq

/-- Inverse translation gives the equivalence, including the zero algebra case. -/
theorem unitaryTranslate_mem_extremePoints_closedBall_iff
    (u : unitary (Unitization ℂ A)) (rho : StrongDual ℂ A) :
    unitaryTranslate u rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ↔
      rho ∈ (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ := by
  constructor
  · intro h
    simpa only [unitaryTranslate_star_translate] using
      unitaryTranslate_mem_extremePoints_closedBall (star u) h
  · exact unitaryTranslate_mem_extremePoints_closedBall u

end MathlibAnnex.Analysis.CStarAlgebra
