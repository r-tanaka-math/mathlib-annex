import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Goldstine's theorem

The closed unit ball of a real or complex normed space is weak-star dense in
the closed unit ball of its bidual.  No separability or completeness
hypothesis is used.
-/

set_option autoImplicit false

open Bornology Topology WeakDual

namespace NormedSpace

universe uK uX

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

private def WeakStarModel (𝕜 : Type uK) (X : Type uX)
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] :=
  StrongDual 𝕜 (StrongDual 𝕜 X)

private def weakStarModelEquiv :
    WeakStarModel 𝕜 X ≃ StrongDual 𝕜 (StrongDual 𝕜 X) :=
  Equiv.refl _

private instance : AddCommGroup (WeakStarModel 𝕜 X) :=
  (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).addCommGroup

private instance {R : Type*} [SMul R (StrongDual 𝕜 (StrongDual 𝕜 X))] :
    SMul R (WeakStarModel 𝕜 X) :=
  (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).smul R

private instance {R : Type*} [Semiring R]
    [Module R (StrongDual 𝕜 (StrongDual 𝕜 X))] :
    Module R (WeakStarModel 𝕜 X) :=
  (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).module R

private instance : IsScalarTower ℝ 𝕜 (WeakStarModel 𝕜 X) :=
  ⟨by
    intro r c z
    apply (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).injective
    change (r • c) • (weakStarModelEquiv z) = r • (c • weakStarModelEquiv z)
    exact smul_assoc r c (weakStarModelEquiv z)⟩

private def weakStarPairing : WeakStarModel 𝕜 X →ₗ[𝕜]
    StrongDual 𝕜 X →ₗ[𝕜] 𝕜 where
  toFun z :=
    { toFun := fun f ↦ weakStarModelEquiv z f
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  map_add' := by intro z w; ext f; rfl
  map_smul' := by intro c z; ext f; rfl

/-- The canonical image, with the weak-star topology on the bidual. -/
def weakStarCanonicalImage (s : Set X) :
    Set (WeakDual 𝕜 (StrongDual 𝕜 X)) :=
  inclusionInDoubleDualWeak 𝕜 X '' (toWeakSpace 𝕜 X '' s)

/-- An operator-norm closed ball, regarded with the weak-star topology. -/
def weakStarClosedBall (r : ℝ) :
    Set (WeakDual 𝕜 (StrongDual 𝕜 X)) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r

private def phase (z : 𝕜) : 𝕜 :=
  if z = 0 then 1 else (‖z‖ : 𝕜) * z⁻¹

private theorem norm_phase {z : 𝕜} (hz : z ≠ 0) :
    ‖phase z‖ = 1 := by
  simp [phase, hz, norm_mul, norm_inv]

private theorem phase_mul {z : 𝕜} (hz : z ≠ 0) :
    phase z * z = (‖z‖ : 𝕜) := by
  simp [phase, hz]

/-- **Goldstine's theorem.**  The canonical image of the closed unit ball is
weak-star dense in the closed unit ball of the bidual. -/
theorem closedBall_subset_closure_weakStarCanonicalImage :
    weakStarClosedBall (𝕜 := 𝕜) (X := X) 1 ⊆
      closure (weakStarCanonicalImage (𝕜 := 𝕜) (X := X)
        (Metric.closedBall 0 1)) := by
  intro omega homega
  let pairing := weakStarPairing (𝕜 := 𝕜) (X := X)
  let W := WeakBilin pairing
  let jm : X →ₗ[𝕜] WeakStarModel 𝕜 X :=
    { toFun := fun x ↦
        (show WeakStarModel 𝕜 X from inclusionInDoubleDual 𝕜 X x)
      map_add' := by
        intro x y
        apply (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).injective
        change inclusionInDoubleDual 𝕜 X (x + y) =
          inclusionInDoubleDual 𝕜 X x + inclusionInDoubleDual 𝕜 X y
        simp
      map_smul' := by
        intro c x
        apply (weakStarModelEquiv (𝕜 := 𝕜) (X := X)).injective
        change inclusionInDoubleDual 𝕜 X (c • x) =
          c • inclusionInDoubleDual 𝕜 X x
        simp }
  let j : X →ₗ[ℝ] W := jm.restrictScalars ℝ
  letI : ContinuousSMul ℝ W := IsScalarTower.continuousSMul 𝕜
  let D : Set W := j '' Metric.closedBall 0 1
  have hconv : Convex ℝ D := by
    exact (convex_closedBall (0 : X) (1 : ℝ)).linear_image j
  let e : WeakDual 𝕜 (StrongDual 𝕜 X) ≃ₜ W :=
    { toFun := fun z ↦
        (show WeakStarModel 𝕜 X from WeakDual.toStrongDual z)
      invFun := fun z ↦ StrongDual.toWeakDual
        (show StrongDual 𝕜 (StrongDual 𝕜 X) from z)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        apply WeakBilin.continuous_of_continuous_eval pairing
        intro f
        exact WeakDual.eval_continuous f
      continuous_invFun := by
        apply WeakDual.continuous_of_continuous_eval
        intro f
        exact WeakBilin.eval_continuous pairing f }
  have he_image : e ''
      weakStarCanonicalImage (𝕜 := 𝕜) (X := X)
        (Metric.closedBall 0 1) = D := by
    ext z
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨inclusionInDoubleDualWeak 𝕜 X (toWeakSpace 𝕜 X x),
        ⟨toWeakSpace 𝕜 X x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  by_contra hnot
  have hnot' : e omega ∉ closure D := by
    intro homegaD
    apply hnot
    rw [e.isEmbedding.closure_eq_preimage_closure_image]
    change e omega ∈ closure (e ''
      weakStarCanonicalImage (𝕜 := 𝕜) (X := X)
        (Metric.closedBall 0 1))
    rw [he_image]
    exact homegaD
  obtain ⟨l, u, hlu, hul⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      hconv.closure isClosed_closure hnot'
  obtain ⟨f, hf⟩ := LinearMap.dualEmbedding_surjective
    pairing l
  have hl (z : W) : l z = weakStarModelEquiv z f := by
    rw [← hf]
    rfl
  have hu_pos : 0 < u := by
    have hzero := hlu (0 : W)
      (subset_closure ⟨0, by simp [Metric.mem_closedBall], by simp [D]⟩)
    rw [hl] at hzero
    change RCLike.re ((0 : StrongDual 𝕜 (StrongDual 𝕜 X)) f) < u at hzero
    simpa using hzero
  have homega_norm : ‖WeakDual.toStrongDual omega‖ ≤ 1 := by
    change dist (WeakDual.toStrongDual omega) 0 ≤ 1 at homega
    calc
      ‖WeakDual.toStrongDual omega‖ =
          dist (WeakDual.toStrongDual omega) 0 :=
        (dist_zero_right (WeakDual.toStrongDual omega)).symm
      _ ≤ 1 := homega
  have hu_norm : u < ‖f‖ := by
    calc
      u < RCLike.re (l (e omega)) := hul
      _ = RCLike.re (WeakDual.toStrongDual omega f) := by
        rw [hl]
        rfl
      _ ≤ ‖WeakDual.toStrongDual omega f‖ := RCLike.re_le_norm _
      _ ≤ ‖WeakDual.toStrongDual omega‖ * ‖f‖ :=
        (WeakDual.toStrongDual omega).le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right homega_norm (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm hu_norm
  have hfx_ne : f x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hfx
    exact (not_lt_of_ge hu_pos.le) hfx
  let c : 𝕜 := phase (f x)
  have hc : ‖c‖ = 1 := norm_phase hfx_ne
  have hcx : c • x ∈ Metric.closedBall (0 : X) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hc, one_mul]
    exact hx.le.trans (by norm_num)
  have hsep := hlu
    (j (c • x))
    (subset_closure ⟨c • x, hcx, rfl⟩)
  have hreal : RCLike.re (l (j (c • x))) = ‖f x‖ := by
    rw [hl]
    change RCLike.re (f (c • x)) = ‖f x‖
    rw [map_smul, smul_eq_mul, phase_mul hfx_ne]
    simp
  rw [hreal] at hsep
  exact (not_lt_of_ge hfx.le) hsep

end

end NormedSpace
