/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryCornerLink

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra NNReal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

-- The scalar function is the literal regularized inverse square root and is
-- genuinely continuous at zero; it is not a discontinuous polar inverse.
example {δ : ℝ≥0} (hδ : 0 < δ) :
    Continuous (cutoffInverseSqrt δ) ∧ cutoffInverseSqrt δ 0 = 0 ∧
      ∀ t, cutoffInverseSqrt δ t = NNReal.sqrt t / max δ t :=
  ⟨continuous_cutoffInverseSqrt hδ, cutoffInverseSqrt_zero δ, fun _ => rfl⟩

-- The same concrete cutoff and the same concrete link have both required bounds.
example (x : A) {δ : ℝ≥0} (hδ : 0 < δ) (hδx : δ < ‖star x * x‖₊) :
    hereditaryCornerCutoff x δ ≠ 0 ∧ ‖hereditaryCornerLink x δ‖ ≤ 1 :=
  ⟨hereditaryCornerCutoff_ne_zero hδx, norm_hereditaryCornerLink_le_one x hδ⟩

-- Square zero is established for the link inside the original nonunital algebra.
example {x : A} (hxx : x * x = 0) (δ : ℝ≥0) :
    hereditaryCornerLink x δ * hereditaryCornerLink x δ = 0 ∧
      hereditaryCornerCutoff x δ * hereditaryCornerLink x δ = 0 :=
  ⟨hereditaryCornerLink_mul_self_eq_zero hxx δ,
    hereditaryCornerCutoff_mul_hereditaryCornerLink_eq_zero hxx δ⟩

-- This consumer constructs the actual equivalence and exposes both ambient formulas.
example (x : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    let c := hereditaryCornerCutoff x δ
    let v := hereditaryCornerLink x δ
    ∃ e : hereditarySubalgebra c ≃⋆ₐ[ℂ] hereditarySubalgebra (v * c * star v),
      (∀ z, (e z : A) = v * (z : A) * star v) ∧
      (∀ w, (e.symm w : A) = star v * (w : A) * v) ∧ Isometry e := by
  dsimp only
  let hc := (hereditaryCornerCutoff_nonneg x δ).isSelfAdjoint
  let hv := star_mul_hereditaryCornerLink_mul_hereditaryCornerCutoff x hδ
  refine ⟨hereditaryConjugateEquiv hc hv, ?_, ?_, isometry_hereditaryConjugateEquiv hc hv⟩
  · intro z
    rfl
  · intro w
    rfl

-- The original inherited norm is preserved for every element of the full closed corner.
example (x : A) {δ : ℝ≥0} (hδ : 0 < δ) {z : A}
    (hz : z ∈ hereditarySubalgebra (hereditaryCornerCutoff x δ)) :
    ‖hereditaryCornerLink x δ * z * star (hereditaryCornerLink x δ)‖ = ‖z‖ :=
  norm_conjugate_of_mem_hereditarySubalgebra
    (hereditaryCornerCutoff_nonneg x δ).isSelfAdjoint
    (star_mul_hereditaryCornerLink_mul_hereditaryCornerCutoff x hδ) hz

-- A hereditary parent contains the actual link as well as the cutoff.
example {a x : A} (hx : x ∈ hereditarySubalgebra a) (δ : ℝ≥0) :
    hereditaryCornerCutoff x δ ∈ hereditarySubalgebra a ∧
      hereditaryCornerLink x δ ∈ hereditarySubalgebra a :=
  ⟨hereditaryCornerCutoff_mem_hereditarySubalgebra hx δ,
    hereditaryCornerLink_mem_hereditarySubalgebra hx δ⟩

-- Neither a nonzero projection nor a separable subalgebra is supplied as a hypothesis.
example (hA : IsAntiliminal A) {a : A} (ha : a ≠ 0) :
    ∃ c v : A, c ∈ hereditarySubalgebra a ∧ v ∈ hereditarySubalgebra a ∧
      0 ≤ c ∧ c ≠ 0 ∧ ‖v‖ ≤ 1 ∧ v * v = 0 ∧ star v * v * c = c ∧ c * v = 0 ∧
      v * c * star v ∈ hereditarySubalgebra a ∧ 0 ≤ v * c * star v ∧
      v * c * star v ≠ 0 ∧ c * (v * c * star v) = 0 ∧ (v * c * star v) * c = 0 :=
  hA.exists_contractive_hereditary_corner_link ha

end MathlibAnnex.Analysis.CStarAlgebra
