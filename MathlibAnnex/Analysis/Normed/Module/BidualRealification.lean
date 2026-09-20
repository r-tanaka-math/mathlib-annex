import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Realification of a complex Banach bidual

The real functional associated with `F ∈ X**` sends a real functional `g`
to `re (F (g.extendRCLike))`.  This is the real bidual point needed when a
single approximation problem contains both linear and conjugate-linear
coordinates.  No complex linearity of the involution is asserted.

C02 controller-authored proof source. Not elaborated or kernel-checked here.
-/
set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.BidualRealification

universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedSpace ℝ Y] [IsScalarTower ℝ ℂ Y]

/-- The canonical real bidual representative of a complex bidual point. -/
def toReal (F : StrongDual ℂ (StrongDual ℂ X)) :
    StrongDual ℝ (StrongDual ℝ X) :=
  (RCLike.reCLM.comp (F.restrictScalars ℝ)).comp
    ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := X)).toContinuousLinearMap)

@[simp] theorem toReal_apply (F : StrongDual ℂ (StrongDual ℂ X))
    (g : StrongDual ℝ X) :
    toReal F g = (F (g.extendRCLike : StrongDual ℂ X)).re := rfl

/-- Realification does not spend any of the closed-ball norm budget. -/
theorem norm_toReal_le (F : StrongDual ℂ (StrongDual ℂ X)) :
    ‖toReal F‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro g
  calc
    ‖toReal F g‖ ≤ ‖F (g.extendRCLike : StrongDual ℂ X)‖ := by
      simpa only [toReal_apply, Real.norm_eq_abs] using
        (Complex.abs_re_le_norm (F (g.extendRCLike : StrongDual ℂ X)))
    _ ≤ ‖F‖ * ‖(g.extendRCLike : StrongDual ℂ X)‖ := F.le_opNorm _
    _ = ‖F‖ * ‖g‖ := by rw [StrongDual.norm_extendRCLike]

@[simp] theorem toReal_canonical (x : X) :
    toReal (NormedSpace.inclusionInDoubleDual ℂ X x) =
      NormedSpace.inclusionInDoubleDual ℝ X x := by
  ext g
  change ((g.extendRCLike : StrongDual ℂ X) x).re = g x
  exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g x

/-- A complex functional is determined by its real part. -/
theorem eq_of_re_eq (f g : StrongDual ℂ X)
    (h : ∀ x, (f x).re = (g x).re) : f = g := by
  ext x
  apply Complex.ext (h x)
  have hI := h (Complex.I • x)
  simpa only [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, neg_inj] using hI

/-- Complexification commutes with a genuinely complex-linear map. -/
theorem extend_comp (g : StrongDual ℝ Y) (T : X →L[ℂ] Y) :
    StrongDual.extendRCLike (𝕜 := ℂ)
      (g.comp (T.restrictScalars ℝ) : StrongDual ℝ X) =
      (g.extendRCLike : StrongDual ℂ Y).comp T := by
  apply eq_of_re_eq
  intro x
  change ((StrongDual.extendRCLike (𝕜 := ℂ)
      (g.comp (T.restrictScalars ℝ) : StrongDual ℝ X)) x).re =
    ((g.extendRCLike : StrongDual ℂ Y) (T x)).re
  calc
    _ = (g.comp (T.restrictScalars ℝ) : StrongDual ℝ X) x := by
      simpa only [RCLike.re_to_complex] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ)
          (g.comp (T.restrictScalars ℝ) : StrongDual ℝ X) x)
    _ = g (T x) := rfl
    _ = _ := by
      simpa only [RCLike.re_to_complex] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g (T x)).symm

/-- Recover a real coefficient identity from a complex coefficient identity. -/
theorem apply_comp (F : StrongDual ℂ (StrongDual ℂ X)) (T : X →L[ℂ] Y)
    (y : Y) (hy : ∀ g : StrongDual ℂ Y, F (g.comp T) = g y)
    (g : StrongDual ℝ Y) :
    toReal F (g.comp (T.restrictScalars ℝ)) = g y := by
  rw [toReal_apply, extend_comp, hy]
  simpa only [RCLike.re_to_complex] using
    (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g y)

end MathlibAnnex.BidualRealification
