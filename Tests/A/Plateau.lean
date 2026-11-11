/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.Hereditary.Plateau

set_option autoImplicit false
noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra NNReal

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

-- The smaller corner is nonzero because its actual cutoff parameter is below the norm.
example {a : A} (ha : 0 ≤ a) {δ : ℝ≥0} (hδa : δ < ‖a‖₊) :
    cfcₙ (fun t : ℝ≥0 => t - δ) a ≠ 0 := cfcₙ_tsub_ne_zero ha hδa

-- Concrete CFC formula for the local unit in the larger original hereditary algebra.
example {a : A} (ha : 0 ≤ a) (δ : ℝ≥0) :
    cfcₙ (fun t : ℝ≥0 => t / max δ t) a ∈ hereditarySubalgebra a :=
  hereditaryPlateauUnit_mem_hereditarySubalgebra ha δ

-- Exact absorption, not an approximate-unit limit assertion.
example (a : A) {δ : ℝ≥0} (hδ : 0 < δ) :
    hereditaryPlateauUnit a δ * cfcₙ (fun t : ℝ≥0 => t - δ) a =
      cfcₙ (fun t : ℝ≥0 => t - δ) a := hereditaryPlateauUnit_mul_cfcₙ_tsub a hδ

-- The absorption extends to arbitrary elements of the full closed hereditary algebra.
example (a : A) {δ : ℝ≥0} (hδ : 0 < δ)
    (z : hereditarySubalgebra (cfcₙ (fun t : ℝ≥0 => t - δ) a)) :
    hereditaryPlateauUnit a δ * (z : A) = (z : A) ∧
      (z : A) * hereditaryPlateauUnit a δ = (z : A) :=
  hereditaryPlateauUnit_mul_eq_self_of_mem a hδ z.property

-- The original C-star norm is exactly one when the fixed corner is nonzero.
example {a : A} (ha : 0 ≤ a) {δ : ℝ≥0} (hδ : 0 < δ) (hδa : δ < ‖a‖₊) :
    ‖hereditaryPlateauUnit a δ‖ = 1 := norm_hereditaryPlateauUnit ha hδ hδa

-- Neither nonzero projections nor a unit of the ambient algebra are required.
example {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ b e : A, 0 ≤ b ∧ b ≠ 0 ∧ b ∈ hereditarySubalgebra a ∧
      0 ≤ e ∧ ‖e‖ ≤ 1 ∧ e ∈ hereditarySubalgebra a ∧ e * b = b ∧ b * e = b :=
  exists_nonzero_hereditary_plateau ha ha0
