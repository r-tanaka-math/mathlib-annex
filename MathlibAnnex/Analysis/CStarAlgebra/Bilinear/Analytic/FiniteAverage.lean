import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Finite real averaging, with the normalization kept explicit

These are finite sums, not integration or an invariant-mean assumption.
All later sign arguments use the same uniform average. SOURCE_UNBUILT.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace MathlibAnnex.CStarBilinear.Analytic

universe u v w
variable {Ω : Type u} [Fintype Ω] [Nonempty Ω]
variable {E : Type v} [AddCommGroup E] [Module ℝ E]
variable {F : Type w} [AddCommGroup F] [Module ℝ F]

/-- Uniform average on an explicitly finite nonempty type. -/
def finiteMean (f : Ω → E) : E := (Fintype.card Ω : ℝ)⁻¹ • ∑ ω, f ω

private theorem cardReal_pos : 0 < (Fintype.card Ω : ℝ) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)

@[simp] theorem finiteMean_zero : finiteMean (fun _ : Ω ↦ (0 : E)) = 0 := by
  simp [finiteMean]

@[simp] theorem finiteMean_const (x : E) : finiteMean (fun _ : Ω ↦ x) = x := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt (cardReal_pos (Ω := Ω))
  calc
    finiteMean (fun _ : Ω ↦ x) =
        (Fintype.card Ω : ℝ)⁻¹ • ∑ _ : Ω, (1 : ℝ) • x := by simp [finiteMean]
    _ = (Fintype.card Ω : ℝ)⁻¹ • ((∑ _ : Ω, (1 : ℝ)) • x) := by
      rw [Finset.sum_smul]
    _ = x := by simp [smul_smul, hc]

theorem finiteMean_congr {f g : Ω → E} (h : ∀ ω, f ω = g ω) :
    finiteMean f = finiteMean g := by
  congr 1
  exact funext h

@[simp] theorem finiteMean_add (f g : Ω → E) :
    finiteMean (fun ω ↦ f ω + g ω) = finiteMean f + finiteMean g := by
  simp [finiteMean, Finset.sum_add_distrib, smul_add]

@[simp] theorem finiteMean_neg (f : Ω → E) :
    finiteMean (fun ω ↦ -f ω) = -finiteMean f := by
  simp [finiteMean]

@[simp] theorem finiteMean_sub (f g : Ω → E) :
    finiteMean (fun ω ↦ f ω - g ω) = finiteMean f - finiteMean g := by
  simp [sub_eq_add_neg, finiteMean_add, finiteMean_neg]

@[simp] theorem finiteMean_smul (r : ℝ) (f : Ω → E) :
    finiteMean (fun ω ↦ r • f ω) = r • finiteMean f := by
  simp [finiteMean, Finset.smul_sum, smul_smul, mul_comm]

@[simp] theorem finiteMean_mul (r : ℝ) (f : Ω → ℝ) :
    finiteMean (fun ω ↦ r * f ω) = r * finiteMean f :=
  finiteMean_smul r f

/-- A scalar coefficient can be averaged before acting on a fixed vector. -/
theorem finiteMean_smul_const (f : Ω → ℝ) (x : E) :
    finiteMean (fun ω ↦ f ω • x) = finiteMean f • x := by
  simp only [finiteMean, ← Finset.sum_smul, smul_smul, smul_eq_mul]

/-- The sum index may be in a universe unrelated to that of the averaging type. -/
theorem finiteMean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → E) :
    finiteMean (fun ω ↦ ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem finiteMean_map (L : E →ₗ[ℝ] F) (f : Ω → E) :
    finiteMean (fun ω ↦ L (f ω)) = L (finiteMean f) := by
  simp [finiteMean, map_smul, map_sum]

@[simp] theorem finiteMean_re (f : Ω → ℂ) :
    finiteMean (fun ω ↦ (f ω).re) = (finiteMean f).re :=
  finiteMean_map Complex.reCLM.toLinearMap f

@[simp] theorem finiteMean_im (f : Ω → ℂ) :
    finiteMean (fun ω ↦ (f ω).im) = (finiteMean f).im :=
  finiteMean_map Complex.imCLM.toLinearMap f

/-- An explicitly supplied finite permutation preserves the average. -/
theorem finiteMean_equiv (e : Ω ≃ Ω) (f : Ω → E) :
    finiteMean (fun ω ↦ f (e ω)) = finiteMean f := by
  unfold finiteMean
  rw [Equiv.sum_comp]

section RealOrder

theorem finiteMean_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    finiteMean f ≤ finiteMean g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ ↦ h ω)
    (inv_nonneg.mpr (cardReal_pos (Ω := Ω)).le)

theorem finiteMean_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteMean f := by
  simpa using finiteMean_mono h

theorem abs_finiteMean_le (f : Ω → ℝ) :
    |finiteMean f| ≤ finiteMean (fun ω ↦ |f ω|) := by
  apply abs_le.mpr
  constructor
  · have h := finiteMean_mono (fun ω ↦ neg_le_abs (f ω))
    rw [finiteMean_neg] at h
    linarith
  · exact finiteMean_mono (fun ω ↦ le_abs_self (f ω))

/-- Cauchy--Schwarz against the constant one, proved by expanding a finite variance. -/
theorem finiteMean_sq_le (f : Ω → ℝ) :
    finiteMean f ^ 2 ≤ finiteMean (fun ω ↦ f ω ^ 2) := by
  have h := finiteMean_nonneg (fun ω ↦ sq_nonneg (f ω - finiteMean f))
  have he : finiteMean (fun ω ↦ (f ω - finiteMean f) ^ 2) =
      finiteMean (fun ω ↦ f ω ^ 2) - finiteMean f ^ 2 := by
    calc
      _ = finiteMean (fun ω ↦ f ω ^ 2 - (2 * finiteMean f) * f ω +
          finiteMean f ^ 2) := by apply finiteMean_congr; intro ω; ring
      _ = _ := by rw [finiteMean_add, finiteMean_sub, finiteMean_mul, finiteMean_const]; ring
  rw [he] at h
  linarith

end RealOrder

section AlgebraOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteMean_order_mono {f g : Ω → A} (h : ∀ ω, f ω ≤ g ω) :
    finiteMean f ≤ finiteMean g := by
  exact smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun ω _ ↦ h ω)
    (inv_nonneg.mpr (cardReal_pos (Ω := Ω)).le)

theorem finiteMean_order_nonneg {f : Ω → A} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteMean f := by
  simpa using finiteMean_order_mono h

end AlgebraOrder
end MathlibAnnex.CStarBilinear.Analytic
