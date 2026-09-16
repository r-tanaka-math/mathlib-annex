import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-!
# Maximal minors selected by ordered rows

A maximal minor of a matrix with `n` columns is obtained by choosing `n` rows.
A finite set of rows does not itself determine the sign of the determinant, so
`MaximalMinorIndex.orderedRows` uses the increasing order on the row type.

The basic algebra is stated over a commutative ring and for an arbitrary linearly
ordered row type.  The bridge from an order embedding is included because it is
the sign-sensitive interface needed by consumers that already carry ordered rows.
-/

noncomputable section

open scoped BigOperators

namespace MathlibAnnex
namespace Matrix

universe u v

/-- An `n`-element set of rows, used to index maximal minors of an `n`-column matrix. -/
abbrev MaximalMinorIndex (n : ℕ) (ι : Type u) [LinearOrder ι] : Type u :=
  ↥(Set.powersetCard ι n)

namespace MaximalMinorIndex

/-- The increasing enumeration of the rows in a maximal-minor index. -/
def orderedRows {n : ℕ} {ι : Type u} [LinearOrder ι]
    (s : MaximalMinorIndex n ι) : Fin n ↪o ι :=
  Set.powersetCard.ofFinEmbEquiv.symm s

/-- The row set underlying an order embedding. -/
noncomputable def ofOrderEmbedding {n : ℕ} {ι : Type u} [LinearOrder ι]
    (ρ : Fin n ↪o ι) : MaximalMinorIndex n ι :=
  Set.powersetCard.ofFinEmbEquiv ρ

/-- Canonical increasing enumeration recovers the original order embedding. -/
@[simp] theorem orderedRows_ofOrderEmbedding {n : ℕ} {ι : Type u} [LinearOrder ι]
    (ρ : Fin n ↪o ι) :
    orderedRows (ofOrderEmbedding ρ) = ρ := by
  exact Set.powersetCard.ofFinEmbEquiv.symm_apply_apply ρ

end MaximalMinorIndex

/-- The square submatrix obtained from an `n`-element row set in increasing order. -/
def maximalSubmatrix {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι]
    (A : _root_.Matrix ι (Fin n) R) (s : MaximalMinorIndex n ι) :
    _root_.Matrix (Fin n) (Fin n) R :=
  A.submatrix s.orderedRows id

/-- The determinant of a maximal submatrix. -/
def maximalMinor {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (s : MaximalMinorIndex n ι) : R :=
  (maximalSubmatrix A s).det

/-- The family of all maximal minors, with the canonical increasing-row sign convention. -/
def maximalMinors {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) : MaximalMinorIndex n ι → R :=
  fun s => maximalMinor A s

/-- The maximal submatrix associated with an order embedding has exactly those rows. -/
@[simp] theorem maximalSubmatrix_ofOrderEmbedding
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι]
    (A : _root_.Matrix ι (Fin n) R) (ρ : Fin n ↪o ι) :
    maximalSubmatrix A (MaximalMinorIndex.ofOrderEmbedding ρ) =
      fun i j => A (ρ i) j := by
  ext i j
  simp [maximalSubmatrix]

/-- The maximal minor associated with an order embedding is the determinant of its row matrix. -/
@[simp] theorem maximalMinor_ofOrderEmbedding
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (ρ : Fin n ↪o ι) :
    maximalMinor A (MaximalMinorIndex.ofOrderEmbedding ρ) =
      _root_.Matrix.det (fun i j => A (ρ i) j) := by
  rw [maximalMinor, maximalSubmatrix_ofOrderEmbedding]

/-- Selecting rows commutes with multiplication by a square right factor. -/
theorem maximalSubmatrix_mul
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [Semiring R]
    (A : _root_.Matrix ι (Fin n) R)
    (L : _root_.Matrix (Fin n) (Fin n) R)
    (s : MaximalMinorIndex n ι) :
    maximalSubmatrix (A * L) s = maximalSubmatrix A s * L := by
  ext i j
  simp [maximalSubmatrix, _root_.Matrix.mul_apply]

/-- A square right factor contributes its determinant to every maximal minor. -/
theorem maximalMinor_mul
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (A : _root_.Matrix ι (Fin n) R)
    (L : _root_.Matrix (Fin n) (Fin n) R)
    (s : MaximalMinorIndex n ι) :
    maximalMinor (A * L) s = maximalMinor A s * L.det := by
  rw [maximalMinor, maximalSubmatrix_mul, _root_.Matrix.det_mul]
  rfl

/-- Vector form of maximal-minor scaling by a square right factor. -/
theorem maximalMinors_mul
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (A : _root_.Matrix ι (Fin n) R)
    (L : _root_.Matrix (Fin n) (Fin n) R) :
    maximalMinors (A * L) = L.det • maximalMinors A := by
  ext s
  simp [maximalMinors, maximalMinor_mul, mul_comm]

/-- Scalar multiplication scales every maximal minor by the `n`th power. -/
theorem maximalMinors_smul
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (c : R) (A : _root_.Matrix ι (Fin n) R) :
    maximalMinors (c • A) = c ^ n • maximalMinors A := by
  ext s
  change _root_.Matrix.det (maximalSubmatrix (c • A) s) =
    c ^ n * _root_.Matrix.det (maximalSubmatrix A s)
  have hsel : maximalSubmatrix (c • A) s = c • maximalSubmatrix A s := by
    ext i j
    rfl
  rw [hsel]
  simp

@[simp] theorem maximalSubmatrix_zero
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [Zero R]
    (s : MaximalMinorIndex n ι) :
    maximalSubmatrix (0 : _root_.Matrix ι (Fin n) R) s = 0 := by
  ext i j
  rfl

/-- The empty determinant is `1`, so the zero-minor formula requires positive size. -/
@[simp] theorem maximalMinor_zero_of_pos
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (hn : 0 < n) (s : MaximalMinorIndex n ι) :
    maximalMinor (0 : _root_.Matrix ι (Fin n) R) s = 0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold maximalMinor
  rw [maximalSubmatrix_zero]
  exact _root_.Matrix.det_zero (inferInstance : Nonempty (Fin n))

@[simp] theorem maximalMinors_zero_of_pos
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (hn : 0 < n) :
    maximalMinors (0 : _root_.Matrix ι (Fin n) R) = 0 := by
  funext s
  simp [maximalMinors, maximalMinor_zero_of_pos hn]

/-- Selecting the rows of a maximal submatrix commutes with matrix-vector multiplication. -/
theorem maximalSubmatrix_mulVec
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [Semiring R]
    (A : _root_.Matrix ι (Fin n) R) (s : MaximalMinorIndex n ι)
    (x : Fin n → R) :
    (maximalSubmatrix A s).mulVec x =
      fun i => A.mulVec x (s.orderedRows i) := by
  funext i
  simp [maximalSubmatrix, _root_.Matrix.mulVec]

/-- One nonzero maximal minor implies injectivity of matrix-vector multiplication. -/
theorem mulVec_injective_of_maximalMinor_ne_zero
    {n : ℕ} {ι : Type u} {K : Type v} [LinearOrder ι] [Field K]
    (A : _root_.Matrix ι (Fin n) K) (s : MaximalMinorIndex n ι)
    (hs : maximalMinor A s ≠ 0) :
    Function.Injective A.mulVec := by
  let g : _root_.Matrix.GeneralLinearGroup (Fin n) K :=
    _root_.Matrix.GeneralLinearGroup.mkOfDetNeZero (maximalSubmatrix A s) hs
  intro x y hxy
  apply (_root_.Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.injective
  change (maximalSubmatrix A s).mulVec x = (maximalSubmatrix A s).mulVec y
  rw [maximalSubmatrix_mulVec, maximalSubmatrix_mulVec]
  funext i
  exact congrFun hxy (s.orderedRows i)

/-- All maximal minors vary continuously with the matrix entries over `ℝ`. -/
theorem maximalMinors_continuous
    {n : ℕ} {ι : Type u} [LinearOrder ι] :
    Continuous
      (maximalMinors : _root_.Matrix ι (Fin n) ℝ → MaximalMinorIndex n ι → ℝ) := by
  apply continuous_pi
  intro s
  change Continuous fun A : _root_.Matrix ι (Fin n) ℝ =>
    _root_.Matrix.det (maximalSubmatrix A s)
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  change Continuous fun A : _root_.Matrix ι (Fin n) ℝ => A (s.orderedRows i) j
  exact continuous_apply_apply _ _

end Matrix
end MathlibAnnex
