import MathlibAnnex.Analysis.Normed.Operator.Determinant
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic

/-!
# Degree-free orientation for global bi-Lipschitz data: basic layer

This candidate isolates the absolute-area-formula part of the argument.  It is
intentionally written on the standard finite Pi space used by Mathlib's
Jacobian theorem.  Source and target connectedness are not fields of the data:
no connectivity is needed for signed transfer, and target preconnectedness is
supplied only at the later constancy theorem.

This browser-produced source is a proof seed.  Its returned status remains
`HANDWRITTEN_UNBUILT` until the exact local Lean lane elaborates and qualifies
it.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MathlibAnnex
namespace BilipschitzOrientation

/-- Global equal-dimensional open-set bi-Lipschitz data.  The explicit
`LipschitzWith` constants avoid a route-local existential Lipschitz wrapper.
Connectivity is deliberately not stored here. -/
structure BiLipschitzOpenData (n : ℕ) where
  source : Set (Fin n → ℝ)
  target : Set (Fin n → ℝ)
  isOpen_source : IsOpen source
  isOpen_target : IsOpen target
  f : (Fin n → ℝ) → (Fin n → ℝ)
  g : (Fin n → ℝ) → (Fin n → ℝ)
  mapsTo_f : MapsTo f source target
  mapsTo_g : MapsTo g target source
  left_inv : Set.LeftInvOn g f source
  right_inv : Set.RightInvOn g f target
  fConstant : ℝ≥0
  lipschitzWith_f : LipschitzWith fConstant f
  gConstant : ℝ≥0
  lipschitzWith_g : LipschitzWith gConstant g
  lower : ℝ
  lower_pos : 0 < lower
  anti : ∀ x y, lower * ‖x - y‖ ≤ ‖f x - f y‖

namespace BiLipschitzOpenData

/-- The forward map admits a Mathlib Lipschitz constant. -/
theorem lipschitz_f {n : ℕ} (D : BiLipschitzOpenData n) :
    ∃ K : ℝ≥0, LipschitzWith K D.f :=
  ⟨D.fConstant, D.lipschitzWith_f⟩

/-- The inverse map admits a Mathlib Lipschitz constant. -/
theorem lipschitz_g {n : ℕ} (D : BiLipschitzOpenData n) :
    ∃ K : ℝ≥0, LipschitzWith K D.g :=
  ⟨D.gConstant, D.lipschitzWith_g⟩

/-- The global lower bound makes the ambient map injective. -/
theorem f_injective {n : ℕ} (D : BiLipschitzOpenData n) :
    Function.Injective D.f := by
  intro x y hxy
  have hle : D.lower * ‖x - y‖ ≤ 0 := by
    simpa [hxy] using D.anti x y
  have hnonneg : 0 ≤ D.lower * ‖x - y‖ :=
    mul_nonneg D.lower_pos.le (norm_nonneg _)
  have hzero : D.lower * ‖x - y‖ = 0 := le_antisymm hle hnonneg
  have hnorm : ‖x - y‖ = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt D.lower_pos)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end BiLipschitzOpenData

/-- In equal finite dimension, a Lipschitz image of a Haar-null set is
Haar-null.  The self-map type is intentional; this theorem does not claim an
unequal-dimensional result. -/
theorem volume_image_eq_zero_of_lipschitzWith {n : ℕ}
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {C : ℝ≥0}
    (hf : LipschitzWith C f) {s : Set (Fin n → ℝ)} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  have hmeasure :
      (μH[(n : ℝ)] : Measure (Fin n → ℝ)) = volume := by
    simpa [Fintype.card_fin] using
      (MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n))
  rw [← hmeasure] at hs ⊢
  apply le_antisymm ?_ bot_le
  calc
    μH[(n : ℝ)] (f '' s)
        ≤ ((C : ℝ≥0∞) ^ (n : ℝ)) * μH[(n : ℝ)] s :=
          hf.hausdorffMeasure_image_le (by positivity) s
    _ = 0 := by rw [hs, mul_zero]

/-- Difference quotients retain a positive global lower bound in the
Fréchet-derivative limit. -/
private theorem fderiv_lower_bound_of_global_lower {n : ℕ}
    {f : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {c : ℝ}
    (_hc : 0 < c)
    (hanti : ∀ u v, c * ‖u - v‖ ≤ ‖f u - f v‖)
    (hfd : HasFDerivAt f A x) (v : Fin n → ℝ) :
    c * ‖v‖ ≤ ‖A v‖ := by
  have hquot : ∀ t : ℝ, t ≠ 0 →
      c * ‖v‖ ≤ ‖t⁻¹ • (f (x + t • v) - f x)‖ := by
    intro t ht
    have h := hanti (x + t • v) x
    simpa [norm_smul, Real.norm_eq_abs, abs_inv, abs_mul, ht,
      mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg t)))
  have htend :
      Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • v) - f x))
        (𝓝[≠] 0) (𝓝 (A v)) := by
    simpa using (hfd.hasLineDerivAt v).tendsto_slope_zero
  have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      c * ‖v‖ ≤ ‖t⁻¹ • (f (x + t • v) - f x)‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hquot t (by simpa using ht)
  exact ge_of_tendsto ((continuous_norm.tendsto (A v)).comp htend) hevent

private theorem injective_of_positive_lower_bound {n : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {c : ℝ} (hc : 0 < c)
    (hA : ∀ v, c * ‖v‖ ≤ ‖A v‖) : Function.Injective A := by
  intro u v huv
  have hzero : A (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have h := hA (u - v)
  rw [hzero, norm_zero] at h
  have : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Every existing derivative of the forward map has the recorded lower
bound. -/
theorem fderiv_lower_bound {n : ℕ} (D : BiLipschitzOpenData n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) (v : Fin n → ℝ) :
    D.lower * ‖v‖ ≤ ‖(fderiv ℝ D.f x) v‖ := by
  exact fderiv_lower_bound_of_global_lower D.lower_pos D.anti
    hdf.hasFDerivAt v

/-- Every existing derivative of the forward map is injective. -/
theorem fderiv_injective {n : ℕ} (D : BiLipschitzOpenData n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) :
    Function.Injective (fderiv ℝ D.f x) := by
  exact injective_of_positive_lower_bound (fderiv ℝ D.f x) D.lower_pos
    (fderiv_lower_bound D hdf)

/-- The derivative determinant is nonzero at differentiability points. -/
theorem det_fderiv_ne_zero {n : ℕ} (D : BiLipschitzOpenData n)
    {x : Fin n → ℝ} (hdf : DifferentiableAt ℝ D.f x) :
    (fderiv ℝ D.f x).det ≠ 0 := by
  change LinearMap.det (fderiv ℝ D.f x).toLinearMap ≠ 0
  intro hdet
  have hker := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet
  exact hker (LinearMap.ker_eq_bot.mpr (fderiv_injective D hdf))

/-- Totalized sign of the forward Jacobian.  At exceptional points the value
`+1` is harmless. -/
def domainJacobianSign {n : ℕ} (D : BiLipschitzOpenData n)
    (x : Fin n → ℝ) : ℝ :=
  if 0 ≤ (fderiv ℝ D.f x).det then 1 else -1

/-- Jacobian sign transported to the target through the specified inverse. -/
def targetJacobianSign {n : ℕ} (D : BiLipschitzOpenData n)
    (y : Fin n → ℝ) : ℝ :=
  domainJacobianSign D (D.g y)

@[simp] theorem abs_domainJacobianSign {n : ℕ}
    (D : BiLipschitzOpenData n) (x : Fin n → ℝ) :
    |domainJacobianSign D x| = 1 := by
  unfold domainJacobianSign
  split <;> norm_num

@[simp] theorem abs_targetJacobianSign {n : ℕ}
    (D : BiLipschitzOpenData n) (y : Fin n → ℝ) :
    |targetJacobianSign D y| = 1 := by
  simp [targetJacobianSign]

/-- The totalized sign restores the signed determinant at each
 differentiability point. -/
theorem det_eq_domainSign_mul_abs {n : ℕ}
    (D : BiLipschitzOpenData n) {x : Fin n → ℝ}
    (hdf : DifferentiableAt ℝ D.f x) :
    (fderiv ℝ D.f x).det =
      domainJacobianSign D x * |(fderiv ℝ D.f x).det| := by
  have hnz := det_fderiv_ne_zero D hdf
  unfold domainJacobianSign
  split_ifs with hnonneg
  · have hpos : 0 < (fderiv ℝ D.f x).det :=
      lt_of_le_of_ne hnonneg (Ne.symm hnz)
    rw [abs_of_pos hpos]
    simp
  · have hneg : (fderiv ℝ D.f x).det < 0 := lt_of_not_ge hnonneg
    rw [abs_of_neg hneg]
    simp

/-- The target image of the Rademacher exceptional set is null. -/
theorem target_exceptional_null {n : ℕ} (D : BiLipschitzOpenData n) :
    volume (D.f '' {x | ¬ DifferentiableAt ℝ D.f x}) = 0 := by
  apply volume_image_eq_zero_of_lipschitzWith D.lipschitzWith_f
  exact ae_iff.mp D.lipschitzWith_f.ae_differentiableAt

/-- Signed transfer is derived from Mathlib's injective absolute Jacobian area
formula.  No signed change-of-variables primitive and no degree theory is used. -/
theorem signed_area_transfer {n : ℕ} (D : BiLipschitzOpenData n)
    {φ : (Fin n → ℝ) → ℝ} (_hφ : IntegrableOn φ D.target) :
    ∫ x in D.source, φ (D.f x) * (fderiv ℝ D.f x).det ∂volume =
      ∫ y in D.target, φ y * targetJacobianSign D y ∂volume := by
  let G : Set (Fin n → ℝ) :=
    D.source ∩ {x | DifferentiableAt ℝ D.f x}
  have hdiff : ∀ᵐ x ∂volume, DifferentiableAt ℝ D.f x :=
    D.lipschitzWith_f.ae_differentiableAt
  have hGmeas : MeasurableSet G := by
    exact D.source_open.measurableSet.inter
      (measurableSet_of_differentiableAt ℝ D.f)
  have hder : ∀ x ∈ G,
      HasFDerivWithinAt D.f (fderiv ℝ D.f x) G x := by
    intro x hx
    exact hx.2.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn D.f G := by
    intro x hx y hy hxy
    exact D.left_inv.injOn hx.1 hy.1 hxy
  have hsign_point : ∀ x ∈ G,
      (fderiv ℝ D.f x).det =
        domainJacobianSign D x * |(fderiv ℝ D.f x).det| := by
    intro x hx
    exact det_eq_domainSign_mul_abs D hx.2
  have hsource_sets : D.source =ᵐ[volume] G := by
    filter_upwards [hdiff] with x hx
    apply propext
    constructor
    · intro hxS
      exact ⟨hxS, hx⟩
    · intro hxG
      exact hxG.1
  have htarget_sets : D.target =ᵐ[volume] D.f '' G := by
    have hbad : ∀ᵐ y ∂volume,
        y ∉ D.f '' {x | ¬ DifferentiableAt ℝ D.f x} := by
      apply ae_iff.mpr
      rw [show {y | ¬ y ∉ D.f '' {x | ¬ DifferentiableAt ℝ D.f x}} =
          D.f '' {x | ¬ DifferentiableAt ℝ D.f x} by ext z; simp]
      exact target_exceptional_null D
    filter_upwards [hbad] with y hybad
    apply propext
    constructor
    · intro hyT
      have hxS : D.g y ∈ D.source := D.mapsTo_g hyT
      have hfx : D.f (D.g y) = y := D.right_inv hyT
      have hxdiff : DifferentiableAt ℝ D.f (D.g y) := by
        by_contra hnot
        exact hybad ⟨D.g y, hnot, hfx⟩
      exact ⟨D.g y, ⟨hxS, hxdiff⟩, hfx⟩
    · rintro ⟨x, hx, rfl⟩
      exact D.mapsTo_f hx.1
  have hdomain_integrand :
      (∫ x in G, φ (D.f x) * (fderiv ℝ D.f x).det ∂volume) =
        ∫ x in G, |(fderiv ℝ D.f x).det| •
          (φ (D.f x) * targetJacobianSign D (D.f x)) ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hGmeas] with x hx
    rw [hsign_point x hx]
    simp [targetJacobianSign, D.left_inv hx.1,
      mul_assoc, mul_left_comm, mul_comm]
  have harea :=
    MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      volume hGmeas hder hinj
        (fun y => φ y * targetJacobianSign D y)
  calc
    (∫ x in D.source, φ (D.f x) * (fderiv ℝ D.f x).det ∂volume) =
        ∫ x in G, φ (D.f x) * (fderiv ℝ D.f x).det ∂volume :=
      setIntegral_congr_set hsource_sets
    _ = ∫ x in G, |(fderiv ℝ D.f x).det| •
          (φ (D.f x) * targetJacobianSign D (D.f x)) ∂volume :=
      hdomain_integrand
    _ = ∫ y in D.f '' G, φ y * targetJacobianSign D y ∂volume :=
      harea.symm
    _ = ∫ y in D.target, φ y * targetJacobianSign D y ∂volume :=
      (setIntegral_congr_set htarget_sets).symm

end BilipschitzOrientation
end MathlibAnnex
