import MathlibAnnex.Algebra.Star.ProjectionEquivalence
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic

/-!
Two explicit coordinate rank-one projections are equivalent in M₂(ℂ),
while their preimages in the diagonal commutative algebra are inequivalent.
This is a source-level counterexample to reflection along an injective
star-algebra inclusion, rather than a failed elaboration test.
-/

set_option autoImplicit false

namespace MatrixProjectionExamples

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def firstProjection : Mat2 := Matrix.single 0 0 1

def secondProjection : Mat2 := Matrix.single 1 1 1

def linkingPartialIsometry : Mat2 := Matrix.single 1 0 1

theorem isPartialIsometry_linkingPartialIsometry : IsPartialIsometry linkingPartialIsometry := by
  simp only [IsPartialIsometry, linkingPartialIsometry, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]

theorem linking_initial : star linkingPartialIsometry * linkingPartialIsometry =
    firstProjection := by
  simp only [linkingPartialIsometry, firstProjection, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]

theorem linking_final : linkingPartialIsometry * star linkingPartialIsometry =
    secondProjection := by
  simp only [linkingPartialIsometry, secondProjection, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]

theorem coordinate_projections_equivalent :
    MurrayVonNeumannEquivalent firstProjection secondProjection := by
  simpa only [linking_initial, linking_final] using
    MurrayVonNeumannEquivalent.of_partial_isometry isPartialIsometry_linkingPartialIsometry

theorem firstProjection_ne_zero : firstProjection ≠ 0 := by
  intro h
  have h00 := congrArg (fun A : Mat2 => A 0 0) h
  have : (1 : ℂ) = 0 := by simpa only [firstProjection, Matrix.single_apply_same, Matrix.zero_apply] using h00
  exact one_ne_zero this

example : ¬ MurrayVonNeumannEquivalent firstProjection (0 : Mat2) := by
  intro h
  exact firstProjection_ne_zero (h.eq_zero_iff.mpr rfl)

def firstCoordinate : Fin 2 → ℂ := Pi.single 0 1

def secondCoordinate : Fin 2 → ℂ := Pi.single 1 1

theorem coordinate_functions_ne : firstCoordinate ≠ secondCoordinate := by
  intro h
  have h0 := congrArg (fun f : Fin 2 → ℂ => f 0) h
  have : (1 : ℂ) = 0 := by simpa [firstCoordinate, secondCoordinate, Pi.single_apply] using h0
  exact one_ne_zero this

theorem coordinate_functions_not_equivalent :
    ¬ MurrayVonNeumannEquivalent firstCoordinate secondCoordinate := by
  intro h
  exact coordinate_functions_ne (h.eq_of_commutative fun a b => mul_comm a b)

theorem diagonal_images_equivalent : MurrayVonNeumannEquivalent
    (Matrix.diagonal firstCoordinate) (Matrix.diagonal secondCoordinate) := by
  simpa only [firstCoordinate, secondCoordinate, Matrix.diagonal_single,
    firstProjection, secondProjection] using coordinate_projections_equivalent

/-- Injectivity of the actual diagonal map does not allow one to pull back
an arbitrary ambient equivalence witness. -/
example : Function.Injective (Matrix.diagonal : (Fin 2 → ℂ) → Mat2) ∧
    ¬ (∀ p q : Fin 2 → ℂ,
      MurrayVonNeumannEquivalent (Matrix.diagonal p) (Matrix.diagonal q) →
        MurrayVonNeumannEquivalent p q) := by
  refine ⟨Matrix.diagonal_injective, ?_⟩
  intro h
  exact coordinate_functions_not_equivalent
    (h firstCoordinate secondCoordinate diagonal_images_equivalent)

end MatrixProjectionExamples

/-- The size-zero matrix algebra is handled as a zero algebra; it is not
used as a nonzero rank-one example. -/
example : MurrayVonNeumannEquivalent
    (0 : Matrix (Fin 0) (Fin 0) ℂ) (1 : Matrix (Fin 0) (Fin 0) ℂ) := by
  have h : (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
  rw [h]
  exact MurrayVonNeumannEquivalent.zero
