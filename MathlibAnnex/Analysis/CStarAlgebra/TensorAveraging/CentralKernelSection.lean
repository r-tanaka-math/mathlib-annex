import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.WeakCompactIdealSupport
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Turning quotient-direction lifts into a coherent central-corner section

A norm-preserving arbitrary lift is not a linear section. Once the identity
e of the kernel is constructed, `(1-e) * lift y` is independent of every
lift choice. We prove the resulting map linear, multiplicative, star
preserving, isometric, and covariant with both source actions. It sends
`1` to `1-e`, not to `1` in the whole domain algebra.

This is a generic C*-algebra theorem. Instantiating it with the raw C01
Banach bidual still requires its compatible C*-realization and the actual
kernel support. No structure instance on that bidual is fabricated here.
C02 controller-authored, unbuilt.
-/
set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.CentralKernelSection

universe u v
variable {M : Type u} [CStarAlgebra M]
variable {N : Type v} [CStarAlgebra N]

/-- Properties delivered by the ideal-support construction. No linear
section, lift, or injectivity-on-corner is included in this record. -/
structure KernelSupport (q : M →⋆ₐ[ℂ] N) where
  e : M
  in_kernel : q e = 0
  star_e : star e = e
  idem : e * e = e
  central : ∀ a : M, e * a = a * e
  identity : ∀ a : M, q a = 0 → e * a = a

namespace KernelSupport

variable {q : M →⋆ₐ[ℂ] N} (s : KernelSupport q)

def projection : M := 1 - s.e

@[simp] theorem projection_star : star s.projection = s.projection := by
  simp [projection, s.star_e]

@[simp] theorem projection_idem : s.projection * s.projection = s.projection := by
  simp only [projection, sub_mul, mul_sub, one_mul, mul_one, s.idem]
  abel

theorem projection_central (a : M) : s.projection * a = a * s.projection := by
  simp only [projection, sub_mul, mul_sub, one_mul, mul_one, s.central]

@[simp] theorem q_projection : q s.projection = 1 := by
  simp [projection, s.in_kernel]

theorem projection_norm_le : ‖s.projection‖ ≤ 1 := by
  have hn := CStarRing.norm_star_mul_self (x := s.projection)
  rw [projection_star, projection_idem] at hn
  nlinarith [norm_nonneg s.projection]

theorem projection_mul_kernel (a : M) (ha : q a = 0) : s.projection * a = 0 := by
  simp only [projection, sub_mul, one_mul, s.identity a ha, sub_self]

/-- Removing kernel ambiguity, the central point of the construction. -/
theorem corner_injective {x y : M}
    (hx : s.projection * x = x) (hy : s.projection * y = y) (hxy : q x = q y) :
    x = y := by
  have hk : q (x - y) = 0 := by simp [hxy]
  have hp := s.projection_mul_kernel (x - y) hk
  rw [mul_sub, hx, hy, sub_eq_zero] at hp
  exact hp

variable (hball : ∀ y : N, ∃ x : M, q x = y ∧ ‖x‖ ≤ ‖y‖)

/-- The arbitrary norm-controlled lift is used only behind the projection. -/
def rawLift (y : N) : M := Classical.choose (hball y)

theorem rawLift_spec (y : N) : q (rawLift hball y) = y ∧ ‖rawLift hball y‖ ≤ ‖y‖ :=
  Classical.choose_spec (hball y)

/-- The eventual section, initially merely a function so all linear laws
have to be proved from uniqueness. -/
def value (y : N) : M := s.projection * rawLift hball y

@[simp] theorem projection_value (y : N) : s.projection * s.value hball y = s.value hball y := by
  simp only [value, ← mul_assoc, projection_idem]

@[simp] theorem q_value (y : N) : q (s.value hball y) = y := by
  simp only [value, map_mul, q_projection, one_mul, (rawLift_spec hball y).1]

theorem value_norm_le (y : N) : ‖s.value hball y‖ ≤ ‖y‖ := by
  calc
    ‖s.value hball y‖ ≤ ‖s.projection‖ * ‖rawLift hball y‖ := norm_mul_le _ _
    _ ≤ 1 * ‖rawLift hball y‖ := mul_le_mul_of_nonneg_right
      s.projection_norm_le (norm_nonneg _)
    _ ≤ ‖y‖ := by simpa using (rawLift_spec hball y).2

theorem value_norm (y : N) : ‖s.value hball y‖ = ‖y‖ := by
  apply le_antisymm (s.value_norm_le hball y)
  calc
    ‖y‖ = ‖q (s.value hball y)‖ := by rw [q_value]
    _ ≤ ‖s.value hball y‖ := NonUnitalStarAlgHom.norm_apply_le q _

/-- Every possible lift yields the same corner value. -/
theorem value_eq_projected_lift (y : N) (x : M) (hx : q x = y) :
    s.value hball y = s.projection * x := by
  apply s.corner_injective (s.projection_value hball y)
  · rw [← mul_assoc, projection_idem]
  · simp only [q_value, map_mul, q_projection, hx, one_mul]

@[simp] theorem value_zero : s.value hball 0 = 0 := by
  apply s.corner_injective (s.projection_value hball 0)
  · simp
  · simp

@[simp] theorem value_add (x y : N) :
    s.value hball (x + y) = s.value hball x + s.value hball y := by
  apply s.corner_injective (s.projection_value hball (x + y))
  · simp only [mul_add, projection_value]
  · simp only [q_value, map_add]

@[simp] theorem value_smul (c : ℂ) (y : N) :
    s.value hball (c • y) = c • s.value hball y := by
  apply s.corner_injective (s.projection_value hball (c • y))
  · simp only [mul_smul_comm, projection_value]
  · simp only [q_value, map_smul]

@[simp] theorem value_mul (x y : N) :
    s.value hball (x * y) = s.value hball x * s.value hball y := by
  apply s.corner_injective (s.projection_value hball (x * y))
  · rw [← mul_assoc, projection_value]
  · simp only [q_value, map_mul]

@[simp] theorem value_star (y : N) : s.value hball (star y) = star (s.value hball y) := by
  apply s.corner_injective (s.projection_value hball (star y))
  · calc
      s.projection * star (s.value hball y) = star (s.value hball y) * s.projection :=
        s.projection_central _
      _ = star (s.projection * s.value hball y) := by simp only [star_mul, projection_star]
      _ = star (s.value hball y) := by rw [projection_value]
  · simp only [q_value, map_star]

/-- The unit is the corner projection. This map need not be unital into M. -/
@[simp] theorem value_one : s.value hball 1 = s.projection := by
  apply s.corner_injective (s.projection_value hball 1) s.projection_idem
  simp

/-- The actual coherent bounded-linear section. -/
def sectionCLM : N →L[ℂ] M :=
  LinearMap.mkContinuous
    { toFun := s.value hball
      map_add' := s.value_add hball
      map_smul' := s.value_smul hball }
    1 (fun y => by
      change ‖s.value hball y‖ ≤ 1 * ‖y‖
      simpa only [one_mul] using s.value_norm_le hball y)

@[simp] theorem sectionCLM_apply (y : N) : s.sectionCLM hball y = s.value hball y := rfl

/-- Multiplicative and star-preserving into M, with no false unital field. -/
def sectionHom : N →⋆ₙₐ[ℂ] M where
  toFun := s.value hball
  map_zero' := s.value_zero hball
  map_add' := s.value_add hball
  map_mul' := s.value_mul hball
  map_smul' := s.value_smul hball
  map_star' := s.value_star hball

/-- Projecting any preimage is exactly section after quotient. -/
theorem value_quotient (a : M) : s.value hball (q a) = s.projection * a :=
  s.value_eq_projected_lift hball (q a) a rfl

theorem value_left_covariance (a : M) (y : N) :
    s.value hball (q a * y) = a * s.value hball y := by
  rw [value_mul, value_quotient]
  calc
    (s.projection * a) * s.value hball y = (a * s.projection) * s.value hball y := by
      rw [projection_central]
    _ = a * s.value hball y := by rw [mul_assoc, projection_value]

theorem value_right_covariance (a : M) (y : N) :
    s.value hball (y * q a) = s.value hball y * a := by
  rw [value_mul, value_quotient, ← mul_assoc,
    ← projection_central s (s.value hball y), projection_value]

/-- Orthogonality to the kernel is two-sided. -/
theorem value_annihilates_kernel (y : N) (a : M) (ha : q a = 0) :
    s.value hball y * a = 0 ∧ a * s.value hball y = 0 := by
  constructor
  · rw [← value_right_covariance s hball a y, ha, mul_zero, value_zero]
  · rw [← value_left_covariance s hball a y, ha, zero_mul, value_zero]

end KernelSupport

export KernelSupport (
  projection projection_star projection_idem projection_central q_projection
  projection_norm_le projection_mul_kernel corner_injective rawLift rawLift_spec
  value projection_value q_value value_norm_le value_norm value_eq_projected_lift
  value_zero value_add value_smul value_mul value_star value_one sectionCLM
  sectionCLM_apply sectionHom value_quotient value_left_covariance
  value_right_covariance value_annihilates_kernel)

end MathlibAnnex.CentralKernelSection
