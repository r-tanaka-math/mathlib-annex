import BanachGeometry.SequenceSpaces.ScalarBasis
import BanachGeometry.SequenceSpaces.C0Blocks
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Explicit BP-basis infrastructure: the standard basis is weakly null; every scalar
evaluation of its image series is absolutely summable; finite signed sums satisfy
the actual operator-norm bound. No unconditional convergence theorem is asserted
here. The no-c₀ → BasisDecay implication is proved downstream in NoC0/BasisDecay
from this infrastructure, rather than supplied as an axiom or typeclass.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace BasisSeries

def rawBasis (n : ℕ) : C0Sum (fun _ : ℕ => ℝ) := C0Sum.single n 1

theorem coordinateDisjoint_rawBasis : C0Sum.CoordinateDisjoint (fun _ : ℕ => ℝ) rawBasis := by
  intro j k hjk i
  by_cases hi : i = j
  · subst i
    exact Or.inr (C0Sum.single_apply_ne (E := fun _ : ℕ => ℝ) k (1 : ℝ) hjk)
  · exact Or.inl (C0Sum.single_apply_ne (E := fun _ : ℕ => ℝ) j (1 : ℝ) hi)

theorem norm_rawBasis_le (n : ℕ) : ‖rawBasis n‖ ≤ 1 := by
  change ‖C0Sum.single (E := fun _ : ℕ => ℝ) n (1 : ℝ)‖ ≤ 1
  rw [C0Sum.norm_single]
  norm_num

theorem weakNull_scalarBasis : WeakNull CanonicalSequences.scalarBasis := by
  intro f
  let e := C0Sum.homogeneousLinearIsometryEquiv ℝ
  have hw := C0Sum.weakNull_of_coordinateDisjoint (fun _ : ℕ => ℝ) rawBasis
    coordinateDisjoint_rawBasis norm_rawBasis_le
      (f.comp e.toLinearIsometry.toContinuousLinearMap)
  exact hw

theorem summable_abs_basis_eval (f : ScalarC0 →L[ℝ] ℝ) :
    Summable (fun n => |f (CanonicalSequences.scalarBasis n)|) :=
  C0Sum.summable_abs_evaluation (fun _ : ℕ => ℝ) rawBasis coordinateDisjoint_rawBasis norm_rawBasis_le
    (f.comp (C0Sum.homogeneousLinearIsometryEquiv ℝ).toLinearIsometry.toContinuousLinearMap)

theorem norm_signed_basis_sum_le (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (s : Finset ℕ) :
    ‖∑ n ∈ s, a n • CanonicalSequences.scalarBasis n‖ ≤ 1 := by
  have h := C0Sum.norm_sum_smul_le_one (fun _ : ℕ => ℝ) rawBasis coordinateDisjoint_rawBasis
    norm_rawBasis_le a ha s
  let e := C0Sum.homogeneousLinearIsometryEquiv ℝ
  have he : (∑ n ∈ s, a n • CanonicalSequences.scalarBasis n) = e (∑ n ∈ s, a n • rawBasis n) := by
    simp only [map_sum, map_smul]; rfl
  rw [he,e.norm_map]
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem summable_abs_image_eval (T : ScalarC0 →L[ℝ] E) (f : E →L[ℝ] ℝ) :
    Summable (fun n => |f (T (CanonicalSequences.scalarBasis n))|) :=
  summable_abs_basis_eval (f.comp T)

theorem weakNull_image_basis (T : ScalarC0 →L[ℝ] E) :
    WeakNull (fun n => T (CanonicalSequences.scalarBasis n)) :=
  fun f => weakNull_scalarBasis (f.comp T)

theorem norm_signed_image_sum_le (T : ScalarC0 →L[ℝ] E)
    (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 1) (s : Finset ℕ) :
    ‖∑ n ∈ s, a n • T (CanonicalSequences.scalarBasis n)‖ ≤ ‖T‖ := by
  simp_rw [← map_smul]
  rw [← map_sum]
  exact (T.le_opNorm _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_signed_basis_sum_le a ha s) (norm_nonneg T))

theorem exists_norming_functional_image_scalarBasis (T : ScalarC0 →L[ℝ] E) (n : ℕ) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ f (T (CanonicalSequences.scalarBasis n)) =
      ‖T (CanonicalSequences.scalarBasis n)‖ :=
  exists_dual_vector'' ℝ (T (CanonicalSequences.scalarBasis n))

end BasisSeries
end BanachGeometry
