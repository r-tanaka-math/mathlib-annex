import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Quantitative strong-star control of bilinear forms

This file isolates the analytic estimate used after a positive-functional
domination theorem has supplied the two controlling functionals.  The gauge
contains both `x*x` and `xx*`, so convergence for an operator and its adjoint
is recorded explicitly.  No functional on a concrete operator algebra is
silently declared normal here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MathlibAnnex.CStarBilinear

universe uA uD

noncomputable section

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {D : Type uD} [NonUnitalCStarAlgebra D]

/-- The two-sided strong-star gauge associated to a bounded functional. -/
def strongStarGauge (φ : A →L[ℂ] ℂ) (x : A) : ℝ :=
  Real.sqrt (‖φ (star x * x)‖ + ‖φ (x * star x)‖)

theorem strongStarGauge_nonneg (φ : A →L[ℂ] ℂ) (x : A) :
    0 ≤ strongStarGauge φ x :=
  Real.sqrt_nonneg _

@[simp]
theorem strongStarGauge_zero (φ : A →L[ℂ] ℂ) :
    strongStarGauge φ 0 = 0 := by
  simp [strongStarGauge]

/-- `B` is controlled by the two strong-star gauges with constant `C`.
This is the exact output expected from a positive-functional domination
theorem; it is deliberately a named hypothesis rather than an assertion that
every bounded bilinear form already has such data. -/
def IsStrongStarDominated
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (φ : A →L[ℂ] ℂ) (ψ : D →L[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ x y, ‖B x y‖ ≤ C * strongStarGauge φ x * strongStarGauge ψ y

/-- The telescoping estimate behind simultaneous bounded-set strong-star
continuity.  The same pair `(x',y')` is used in both error terms. -/
theorem norm_sub_le_of_strongStarDominated
    {B : A →L[ℂ] D →L[ℂ] ℂ}
    {φ : A →L[ℂ] ℂ} {ψ : D →L[ℂ] ℂ} {C : ℝ}
    (hB : IsStrongStarDominated B φ ψ C)
    (x x' : A) (y y' : D) :
    ‖B x y - B x' y'‖ ≤
      C * strongStarGauge φ (x - x') * strongStarGauge ψ y +
        C * strongStarGauge φ x' * strongStarGauge ψ (y - y') := by
  have hsplit :
      B x y - B x' y' = B (x - x') y + B x' (y - y') := by
    rw [ContinuousLinearMap.map_sub₂, map_sub]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (hB _ _) (hB _ _))

/-- Uniform version of the preceding estimate.  It is suitable for a finite
family of forms because the bounds can be chosen once and then reused for
every member of that family. -/
theorem norm_sub_lt_of_uniform_strongStar
    {B : A →L[ℂ] D →L[ℂ] ℂ}
    {φ : A →L[ℂ] ℂ} {ψ : D →L[ℂ] ℂ} {C δ M ε : ℝ}
    (hB : IsStrongStarDominated B φ ψ C)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hε : 2 * C * δ * M < ε)
    {x x' : A} {y y' : D}
    (hx : strongStarGauge φ (x - x') < δ)
    (hx' : strongStarGauge φ x' ≤ M)
    (hy : strongStarGauge ψ (y - y') < δ)
    (hy' : strongStarGauge ψ y ≤ M) :
    ‖B x y - B x' y'‖ < ε := by
  have h₁ : C * strongStarGauge φ (x - x') * strongStarGauge ψ y ≤
      C * δ * M := by
    calc
      C * strongStarGauge φ (x - x') * strongStarGauge ψ y ≤
          C * δ * strongStarGauge ψ y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx.le hC)
          (strongStarGauge_nonneg ψ y)
      _ ≤ C * δ * M :=
        mul_le_mul_of_nonneg_left hy' (mul_nonneg hC hδ)
  have h₂ : C * strongStarGauge φ x' * strongStarGauge ψ (y - y') ≤
      C * M * δ := by
    calc
      C * strongStarGauge φ x' * strongStarGauge ψ (y - y') ≤
          C * M * strongStarGauge ψ (y - y') :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx' hC)
          (strongStarGauge_nonneg ψ (y - y'))
      _ ≤ C * M * δ :=
        mul_le_mul_of_nonneg_left hy.le (mul_nonneg hC hM)
  have hmain := norm_sub_le_of_strongStarDominated hB x x' y y'
  calc
    ‖B x y - B x' y'‖ ≤
        C * strongStarGauge φ (x - x') * strongStarGauge ψ y +
          C * strongStarGauge φ x' * strongStarGauge ψ (y - y') := hmain
    _ ≤ C * δ * M + C * M * δ := add_le_add h₁ h₂
    _ = 2 * C * δ * M := by ring
    _ < ε := hε

/-- A finite family version: one common strong-star neighbourhood controls
all evaluations.  This records the simultaneity needed by convex-closure
arguments instead of choosing a different approximant for each test. -/
theorem finite_norm_sub_lt_of_uniform_strongStar
    {ι : Type*} [Fintype ι]
    (B : ι → A →L[ℂ] D →L[ℂ] ℂ)
    (φ : ι → A →L[ℂ] ℂ) (ψ : ι → D →L[ℂ] ℂ)
    {C δ M ε : ℝ}
    (hB : ∀ i, IsStrongStarDominated (B i) (φ i) (ψ i) C)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hε : 2 * C * δ * M < ε)
    {x x' : A} {y y' : D}
    (hx : ∀ i, strongStarGauge (φ i) (x - x') < δ)
    (hx' : ∀ i, strongStarGauge (φ i) x' ≤ M)
    (hy : ∀ i, strongStarGauge (ψ i) (y - y') < δ)
    (hy' : ∀ i, strongStarGauge (ψ i) y ≤ M) :
    ∀ i, ‖B i x y - B i x' y'‖ < ε := by
  intro i
  exact norm_sub_lt_of_uniform_strongStar (hB i) hC hδ hM hε
    (hx i) (hx' i) (hy i) (hy' i)

end

end MathlibAnnex.CStarBilinear
