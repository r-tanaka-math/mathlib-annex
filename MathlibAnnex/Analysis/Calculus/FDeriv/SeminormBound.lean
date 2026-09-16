import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Directional seminorm bounds for derivatives

A global increment bound by a seminorm passes to every directional derivative.
The almost everywhere statement uses the reference Lebesgue measure and retains
an arbitrary restricted set, including the model closed unit ball.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace MathlibAnnex.FDeriv

/-- A seminorm increment bound passes to the derivative in each direction. -/
theorem norm_apply_le_seminorm_of_lipschitz {n N : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (hf : ∀ x y, ‖f x - f y‖ ≤ p (x - y)) {x : Fin n → ℝ}
    (hx : DifferentiableAt ℝ f x) : ∀ v, ‖(fderiv ℝ f x) v‖ ≤ p v := by
  have derivative_bound {φ : ℝ → (Fin N → ℝ)} {d : Fin N → ℝ} {C : ℝ}
      (hφ : HasDerivAt φ d 0)
      (hbound : ∀ t : ℝ, ‖φ t - φ 0‖ ≤ |t| * C) : ‖d‖ ≤ C := by
    have hquot : Tendsto (fun t : ℝ => t⁻¹ • (φ t - φ 0)) (𝓝[≠] 0) (𝓝 d) := by
      simpa using hφ.tendsto_slope_zero
    have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖t⁻¹ • (φ t - φ 0)‖ ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      calc
        ‖t⁻¹ • (φ t - φ 0)‖ = |t|⁻¹ * ‖φ t - φ 0‖ := by
          simp [norm_smul, Real.norm_eq_abs]
        _ ≤ |t|⁻¹ * (|t| * C) :=
          mul_le_mul_of_nonneg_left (hbound t) (inv_nonneg.mpr (abs_nonneg t))
        _ = C := by field_simp [abs_ne_zero.mpr ht0]
    exact le_of_tendsto ((continuous_norm.tendsto d).comp hquot) hevent
  intro v
  let φ : ℝ → (Fin N → ℝ) := fun t => f (x + t • v)
  have hφ : HasDerivAt φ ((fderiv ℝ f x) v) 0 := by
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
    simpa [φ, Function.comp_def] using
      hx.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hbound : ∀ t : ℝ, ‖φ t - φ 0‖ ≤ |t| * p v := by
    intro t
    calc
      ‖φ t - φ 0‖ ≤ p ((x + t • v) - (x + 0 • v)) := hf _ _
      _ = p (t • v) := by
        exact congrArg (fun w : Fin n → ℝ => p w) (by module)
      _ = |t| * p v := by simpa [Real.norm_eq_abs] using map_smul_eq_mul p t v
  exact derivative_bound hφ hbound

/-- The directional bound holds almost everywhere on every restricted set. -/
theorem ae_norm_apply_le_seminorm_of_lipschitz {n N : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) {f : (Fin n → ℝ) → (Fin N → ℝ)}
    (U : NNReal) (hu : ∀ x, p x ≤ U * ‖x‖)
    (hf : ∀ x y, ‖f x - f y‖ ≤ p (x - y)) (s : Set (Fin n → ℝ)) :
    ∀ᵐ x ∂volume.restrict s, ∀ v, ‖(fderiv ℝ f x) v‖ ≤ p v := by
  have hl : LipschitzWith U f := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm] using (hf x y).trans (hu (x - y))
  have hd : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := hl.ae_differentiableAt
  have hdr : ∀ᵐ x ∂volume.restrict s, DifferentiableAt ℝ f x := ae_restrict_of_ae hd
  filter_upwards [hdr] with x hx
  exact norm_apply_le_seminorm_of_lipschitz p hf hx

end MathlibAnnex.FDeriv
