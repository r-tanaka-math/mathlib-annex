/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.NormLiftScalar
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Norm-minimizing representatives of C-star homomorphism fibers

The construction applies to every nonunital star homomorphism of C-star
algebras; it does not assume its range is closed or a quotient is already a
C-star algebra. For `r = ‖q a‖ > 0`, put
`c = cfcₙ (normLiftCutoff r) (star a * a)` and `b = a - a*c`.
Then `q c = 0` and `star b*b = cfcₙ (normLiftEnergy r) (star a*a)`.
The zero fiber is handled separately. No element is divided by its norm,
and no unjustified unitary lifting or image-norm transfer is used.
-/

set_option autoImplicit false
noncomputable section
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]

/-- Polynomial compatibility needed to estimate the corrected lift. Each
factor used with `cfcₙ` is continuous and zero-preserving. -/
theorem cfcₙ_normLiftEnergy (a : A) {r : ℝ} (hr : 0 < r) :
    cfcₙ (normLiftEnergy r) (star a * a) =
      (star a * a) - (star a * a) * cfcₙ (normLiftCutoff r) (star a * a) -
        cfcₙ (normLiftCutoff r) (star a * a) * (star a * a) +
        cfcₙ (normLiftCutoff r) (star a * a) * (star a * a) *
          cfcₙ (normLiftCutoff r) (star a * a) := by
  let d := star a * a
  let f := normLiftCutoff r
  have hd : IsSelfAdjoint d := .star_mul_self a
  have hf : ContinuousOn f (quasispectrum ℝ d) := (continuous_normLiftCutoff hr).continuousOn
  have hf0 : f 0 = 0 := normLiftCutoff_zero hr
  have hid : ContinuousOn (fun t : ℝ => t) (quasispectrum ℝ d) := continuous_id.continuousOn
  have hm1 := cfcₙ_mul (fun t : ℝ => t) f d hid rfl hf hf0
  have hm2 := cfcₙ_mul f (fun t : ℝ => t) d hf hf0 hid rfl
  have hm3 := cfcₙ_mul (fun t => f t * t) f d (hf.mul hid) (by simp) hf hf0
  have hs1 := cfcₙ_sub (fun t : ℝ => t) (fun t => t * f t) d
    hid rfl (hid.mul hf) (by simp)
  have hs2 := cfcₙ_sub (fun t => t - t * f t) (fun t => f t * t) d
    (hid.sub (hid.mul hf)) (by simp) (hf.mul hid) (by simp)
  have ha := cfcₙ_add (fun t => t - t * f t - f t * t) (fun t => f t * t * f t) d
    ((hid.sub (hid.mul hf)).sub (hf.mul hid)) (by simp)
    ((hf.mul hid).mul hf) (by simp)
  change cfcₙ (fun t => t - t * f t - f t * t + f t * t * f t) d = _
  simp only [ha, hs2, hs1, hm1, hm2, hm3, cfcₙ_id' ℝ d hd]
  rfl

/-- The corrected lift has the same image and no more than the image norm.
This statement does not presuppose completeness of the range. -/
theorem exists_same_image_norm_le (q : A →⋆ₙₐ[ℂ] B) (a : A) :
    ∃ b : A, q b = q a ∧ ‖b‖ ≤ ‖q a‖ := by
  by_cases hz : q a = 0
  · exact ⟨0, by simpa only [map_zero] using hz.symm, by simp [hz]⟩
  let r : ℝ := ‖q a‖
  have hr : 0 < r := norm_pos_iff.mpr hz
  let d := star a * a
  let c : A := cfcₙ (normLiftCutoff r) d
  let b := a - a * c
  have hd : IsSelfAdjoint d := .star_mul_self a
  have hqd : IsSelfAdjoint (q d) := hd.map q
  have hqc : q c = 0 := by
    rw [show q c = cfcₙ (normLiftCutoff r) (q d) from
      q.map_cfcₙ _ d (continuous_normLiftCutoff hr).continuousOn
        (normLiftCutoff_zero hr) (map_continuous q) hd hqd]
    calc
      cfcₙ (normLiftCutoff r) (q d) = cfcₙ (0 : ℝ → ℝ) (q d) := by
        apply cfcₙ_congr
        intro t ht
        apply normLiftCutoff_eq_zero_of_le_sq hr
        calc
          t ≤ ‖t‖ := by simpa only [Real.norm_eq_abs] using le_abs_self t
          _ ≤ ‖q d‖ :=
            NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le (q d) ht hqd
          _ = r ^ 2 := by
            simp only [d, r, map_mul, map_star, CStarRing.norm_star_mul_self, pow_two]
      _ = 0 := cfcₙ_zero ℝ (q d)
  have hc : IsSelfAdjoint c := IsSelfAdjoint.cfcₙ
  have hcstar : star c = c := hc
  have hprod : star b * b = d - d * c - c * d + c * d * c := by
    simp only [b, star_sub, star_mul, hcstar, mul_sub, sub_mul, mul_assoc, d]
    abel
  have hb : ‖b‖ ≤ r := by
    have he : ‖star b * b‖ ≤ r ^ 2 := by
      rw [hprod, ← cfcₙ_normLiftEnergy a hr]
      apply norm_cfcₙ_le
      intro t ht
      exact norm_normLiftEnergy_le hr
        (quasispectrum_nonneg_of_nonneg (star a * a) (star_mul_self_nonneg a) t ht)
    rw [CStarRing.norm_star_mul_self] at he
    nlinarith [norm_nonneg b]
  exact ⟨b, by simp [b, map_sub, map_mul, hqc], hb⟩

/-- Every fiber contains a representative whose norm is exactly the image norm. -/
theorem exists_same_image_norm_eq (q : A →⋆ₙₐ[ℂ] B) (a : A) :
    ∃ b : A, q b = q a ∧ ‖b‖ = ‖q a‖ := by
  obtain ⟨b, heq, hle⟩ := exists_same_image_norm_le q a
  refine ⟨b, heq, le_antisymm hle ?_⟩
  rw [← heq]
  exact NonUnitalStarAlgHom.norm_apply_le q b

/-- A surjective C-star homomorphism admits norm-preserving representatives;
this is stronger than epsilon representatives of a general Banach quotient. -/
theorem exists_preimage_norm_eq_of_surjective
    (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q) (b : B) :
    ∃ a : A, q a = b ∧ ‖a‖ = ‖b‖ := by
  obtain ⟨a, rfl⟩ := hq b
  exact exists_same_image_norm_eq q a

end MathlibAnnex.Analysis.CStarAlgebra
