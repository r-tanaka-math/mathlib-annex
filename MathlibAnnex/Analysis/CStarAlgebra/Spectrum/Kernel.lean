/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.NormAttainment
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.RepresentationEquivalence
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Kernels of nonunital representations as actual two-sided ideals

The ideal is Mathlib's `TwoSidedIdeal.ker`, not a geometric-spectrum point.
Closedness, complex scalar closure and star closure are proved separately.
For a nonzero irreducible representation the kernel is meet-prime among ALL
algebraic two-sided ideals. The proof uses a middle algebra element carrying
one nonzero represented vector to another, and does not require the ideals
to be norm closed, star closed, or complex subspaces.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private def kernelContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The genuine algebraic two-sided ideal which is the kernel of the representation. -/
def kernelIdeal (pi : NonUnitalCStarRepresentation A H) : TwoSidedIdeal A :=
  TwoSidedIdeal.ker pi

@[simp]
theorem mem_kernelIdeal (pi : NonUnitalCStarRepresentation A H) (a : A) :
    a ∈ kernelIdeal pi ↔ pi a = 0 := TwoSidedIdeal.mem_ker pi

/-- The ideal and the continuous-linear kernel have exactly the same carrier. -/
theorem coe_kernelIdeal_eq_ker (pi : NonUnitalCStarRepresentation A H) :
    (kernelIdeal pi : Set A) = (((kernelContinuousMap pi).ker) : Set A) := by
  ext a
  exact mem_kernelIdeal pi a

/-- Representation kernels are norm closed, including the zero representation. -/
theorem isClosed_kernelIdeal (pi : NonUnitalCStarRepresentation A H) :
    IsClosed (kernelIdeal pi : Set A) := by
  have heq : (kernelIdeal pi : Set A) = {a : A | pi a = 0} := by
    ext a
    exact mem_kernelIdeal pi a
  rw [heq]
  exact isClosed_eq (kernelContinuousMap pi).continuous continuous_const

@[simp]
theorem star_mem_kernelIdeal_iff (pi : NonUnitalCStarRepresentation A H) (a : A) :
    star a ∈ kernelIdeal pi ↔ a ∈ kernelIdeal pi := by
  simp only [mem_kernelIdeal, map_star, star_eq_zero]

/-- Scalar stability is not part of the bare `TwoSidedIdeal` structure. -/
theorem smul_mem_kernelIdeal (pi : NonUnitalCStarRepresentation A H) (c : ℂ)
    {a : A} (ha : a ∈ kernelIdeal pi) : c • a ∈ kernelIdeal pi := by
  rw [mem_kernelIdeal] at ha ⊢
  rw [map_smul, ha, smul_zero]

theorem kernelIdeal_ne_top (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsNonzero) :
    kernelIdeal pi ≠ ⊤ := by
  intro htop
  obtain ⟨a, ha⟩ := hpi
  apply ha
  apply (mem_kernelIdeal pi a).1
  rw [htop]
  exact TwoSidedIdeal.mem_top A

/-- Nonzero represented action forces the original algebra to be nontrivial. -/
theorem nontrivial_algebra_of_isNonzero (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsNonzero) : Nontrivial A := by
  obtain ⟨a, ha⟩ := hpi
  exact ⟨⟨a, 0, fun h => ha (by rw [h, map_zero])⟩⟩

/-- Equivalence, not equality of kernels, is the premise. No irreducibility is needed. -/
theorem UnitaryEquivalent.kernelIdeal_eq {pi : NonUnitalCStarRepresentation A H}
    {sigma : NonUnitalCStarRepresentation A K} (h : pi.UnitaryEquivalent sigma) :
    kernelIdeal pi = kernelIdeal sigma := by
  obtain ⟨U, hU⟩ := h
  apply TwoSidedIdeal.ext
  intro a
  simp only [mem_kernelIdeal]
  constructor
  · intro ha
    apply ContinuousLinearMap.ext
    intro y
    calc
      sigma a y = U (pi a (U.symm y)) := by rw [hU, U.apply_symm_apply]
      _ = 0 := by simp only [ha, ContinuousLinearMap.zero_apply, map_zero]
  · intro ha
    apply ContinuousLinearMap.ext
    intro x
    apply U.injective
    simp only [hU, ha, ContinuousLinearMap.zero_apply, map_zero]

/-- The original-algebra orbit of any nonzero vector is all of H. Unit-vector
transitivity is used only in its supplied original-A form; no unit is inserted in A. -/
theorem apply_surjective_of_isIrreducible (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) {x : H} (hx : x ≠ 0) :
    Function.Surjective (fun a : A => pi a x) := by
  classical
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp only [map_zero, ContinuousLinearMap.zero_apply, hy]⟩
  have hnx : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hx).ne'
  have hny : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hy).ne'
  have hxunit : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hyunit : ‖(‖y‖ : ℂ)⁻¹ • y‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  obtain ⟨b, -, hb⟩ := exists_norm_eq_one_and_apply_eq_of_isIrreducible pi hpi
    ((‖x‖ : ℂ)⁻¹ • x) ((‖y‖ : ℂ)⁻¹ • y) hxunit hyunit
  have hbx : pi b x = (‖x‖ : ℂ) • ((‖y‖ : ℂ)⁻¹ • y) := by
    calc
      pi b x = pi b ((‖x‖ : ℂ) • ((‖x‖ : ℂ)⁻¹ • x)) := by
        rw [smul_smul, mul_inv_cancel₀ hnx, one_smul]
      _ = (‖x‖ : ℂ) • ((‖y‖ : ℂ)⁻¹ • y) := by rw [map_smul, hb]
  refine ⟨((‖y‖ : ℂ) / (‖x‖ : ℂ)) • b, ?_⟩
  change pi (((‖y‖ : ℂ) / (‖x‖ : ℂ)) • b) x = y
  rw [map_smul]
  change ((‖y‖ : ℂ) / (‖x‖ : ℂ)) • (pi b x) = y
  rw [hbx, smul_smul, smul_smul]
  have hc : (‖y‖ : ℂ) / (‖x‖ : ℂ) * (‖x‖ : ℂ) * (‖y‖ : ℂ)⁻¹ = 1 := by
    field_simp [hnx, hny]
  rw [hc, one_smul]

/-- Primitive kernels are meet-prime. The middle factor comes from the actual
irreducible action on H; no quotient simplicity or equality-kernel classification is used. -/
theorem inf_le_kernelIdeal_iff (pi : NonUnitalCStarRepresentation A H)
    (hpi : pi.IsIrreducible) (I J : TwoSidedIdeal A) :
    I ⊓ J ≤ kernelIdeal pi ↔ I ≤ kernelIdeal pi ∨ J ≤ kernelIdeal pi := by
  classical
  constructor
  · intro hIJ
    by_cases hI : I ≤ kernelIdeal pi
    · exact Or.inl hI
    right
    have hIex : ∃ a : A, a ∈ I ∧ a ∉ kernelIdeal pi := by
      by_contra! h
      exact hI h
    obtain ⟨a, haI, ha⟩ := hIex
    have ha0 : pi a ≠ 0 := fun h => ha ((mem_kernelIdeal pi a).2 h)
    obtain ⟨x, hx⟩ : ∃ x : H, pi a x ≠ 0 := by
      by_contra! h
      exact ha0 (ContinuousLinearMap.ext h)
    intro b hbJ
    apply (mem_kernelIdeal pi b).2
    by_contra hb0
    obtain ⟨y, hy⟩ : ∃ y : H, pi b y ≠ 0 := by
      by_contra! h
      exact hb0 (ContinuousLinearMap.ext h)
    obtain ⟨c, hc⟩ := apply_surjective_of_isIrreducible pi hpi hy x
    change pi c (pi b y) = x at hc
    have hzI : a * c * b ∈ I :=
      I.mul_mem_right (a * c) b (I.mul_mem_right a c haI)
    have hzJ : a * c * b ∈ J := J.mul_mem_left (a * c) b hbJ
    have hz0 : pi (a * c * b) = 0 :=
      (mem_kernelIdeal pi _).1 (hIJ (show a * c * b ∈ I ⊓ J from ⟨hzI, hzJ⟩))
    have h := congrArg (fun T : H →L[ℂ] H => T y) hz0
    rw [map_mul, map_mul] at h
    change pi a (pi c (pi b y)) = 0 at h
    rw [hc] at h
    exact hx h
  · rintro (hI | hJ)
    · exact inf_le_left.trans hI
    · exact inf_le_right.trans hJ

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
