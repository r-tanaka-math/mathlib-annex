/- Normalized interpolation between two orthogonal unit code levels.
The exact constant is 4. No global Omega is assumed.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.HilbertSums.Coding.Bounds

noncomputable section
open scoped InnerProductSpace
namespace BanachGeometry.HilbertSums.Coding
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def affineSegment (u v : V) (s : ℝ) : V := (1 - s) • u + s • v
def unitSegment (u v : V) (s : ℝ) : V := NormedSpace.normalize (affineSegment u v s)

theorem norm_affineSegment_sq (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s : ℝ) :
    ‖affineSegment u v s‖ ^ 2 = (1 - s) ^ 2 + s ^ 2 := by
  simp [affineSegment, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, hu, hv, real_inner_smul_left, real_inner_smul_right, huv]

theorem one_half_le_norm_affineSegment_sq (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s : ℝ) : (1 / 2 : ℝ) ≤ ‖affineSegment u v s‖ ^ 2 := by
  rw [norm_affineSegment_sq u v hu hv huv]
  nlinarith [sq_nonneg (2 * s - 1)]

theorem affineSegment_ne_zero (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s : ℝ) : affineSegment u v s ≠ 0 := by
  intro h
  have hl := one_half_le_norm_affineSegment_sq u v hu hv huv s
  rw [h, norm_zero] at hl
  norm_num at hl

theorem norm_unitSegment (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s : ℝ) : ‖unitSegment u v s‖ = 1 :=
  NormedSpace.norm_normalize (affineSegment_ne_zero u v hu hv huv s)

theorem unitSegment_zero (u v : V) (hu : ‖u‖ = 1) : unitSegment u v 0 = u := by
  simp [unitSegment, affineSegment, NormedSpace.normalize_eq_self_of_norm_eq_one hu]

theorem unitSegment_one (u v : V) (hv : ‖v‖ = 1) : unitSegment u v 1 = v := by
  simp [unitSegment, affineSegment, NormedSpace.normalize_eq_self_of_norm_eq_one hv]

theorem affineSegment_sub (u v : V) (s t : ℝ) :
    affineSegment u v s - affineSegment u v t = (s - t) • (v - u) := by
  unfold affineSegment
  module

theorem norm_affineSegment_sub_sq (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s t : ℝ) :
    ‖affineSegment u v s - affineSegment u v t‖ ^ 2 = 2 * (s - t) ^ 2 := by
  rw [affineSegment_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sub_sq_real, real_inner_comm u v, huv, hu, hv]
  ring

/-- Exact R6 estimate on a normalized segment; valid in particular for s,t in [0,1]. -/
theorem norm_unitSegment_sub_le (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u, v⟫_ℝ = 0) (s t : ℝ) :
    ‖unitSegment u v s - unitSegment u v t‖ ≤ 4 * |s - t| := by
  let D := ‖unitSegment u v s - unitSegment u v t‖
  have hscaled : ‖affineSegment u v s‖ * D ≤
      2 * ‖affineSegment u v s - affineSegment u v t‖ :=
    norm_mul_norm_normalize_sub_le _ _ (affineSegment_ne_zero u v hu hv huv t)
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ ‖affineSegment u v s‖ * D)
    (by positivity)).2 hscaled
  rw [mul_pow, mul_pow, norm_affineSegment_sub_sq u v hu hv huv] at hsq
  have hlow := mul_le_mul_of_nonneg_right
    (one_half_le_norm_affineSegment_sq u v hu hv huv s) (sq_nonneg D)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  change D ^ 2 ≤ (4 * |s - t|) ^ 2
  rw [mul_pow, sq_abs]
  nlinarith

end BanachGeometry.HilbertSums.Coding
