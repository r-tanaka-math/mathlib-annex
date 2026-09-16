import MathlibAnnex.LinearAlgebra.Matrix.MaximalMinor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Factorization from proportional oriented maximal minors

This candidate separates the sign-sensitive, ordered-row theorem from the
adapter to `MathlibAnnex.Matrix.maximalMinor`, whose indices use increasing row
order.  The matrix convention is `source = target * factor`, corresponding to
`target ∘ factor = source` for column-vector linear maps.

Canonical set-indexed minors are transported to arbitrary ordered row tuples
by sorting and a common determinant sign. Noninjective tuples are handled by
the repeated-row determinant theorem, and dimension zero is explicit.
-/

noncomputable section

open scoped Matrix

namespace MathlibAnnex
namespace Matrix

universe u v

/-- Determinant of the square matrix obtained from an ordered tuple of rows.
The tuple is allowed to repeat rows; then the determinant vanishes. -/
def orientedMaximalMinor {n : ℕ} {ι : Type u} {R : Type v} [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (rows : Fin n → ι) : R :=
  (A.submatrix rows id).det

/-- All ordered maximal minors of `source` equal `scale` times those of
`target`.  Repeated-row tuples are included to make row replacement sign-free. -/
def OrientedMaximalMinorsProportional
    {n : ℕ} {ι : Type u} {R : Type v} [CommRing R]
    (source target : _root_.Matrix ι (Fin n) R) (scale : R) : Prop :=
  ∀ rows : Fin n → ι,
    orientedMaximalMinor source rows =
      scale * orientedMaximalMinor target rows

/-- Canonical increasing-row maximal minors are pointwise proportional. -/
def MaximalMinorsProportional
    {n : ℕ} {ι : Type u} {R : Type v}
    [LinearOrder ι] [CommRing R]
    (source target : _root_.Matrix ι (Fin n) R) (scale : R) : Prop :=
  ∀ s : MaximalMinorIndex n ι,
    maximalMinor source s = scale * maximalMinor target s

/-- The canonical order-embedding bridge converts a maximal-minor relation
at one increasing row tuple to the oriented convention without a sign. -/
theorem orientedMaximalMinor_eq_of_orderEmbedding
    {n : ℕ} {ι : Type u} {R : Type v}
    [LinearOrder ι] [CommRing R]
    (source target : _root_.Matrix ι (Fin n) R) (scale : R)
    (hminor : MaximalMinorsProportional source target scale)
    (rows : Fin n ↪o ι) :
    orientedMaximalMinor source rows =
      scale * orientedMaximalMinor target rows := by
  have h := hminor (MaximalMinorIndex.ofOrderEmbedding rows)
  change _root_.Matrix.det (fun i j => source (rows i) j) =
    scale * _root_.Matrix.det (fun i j => target (rows i) j)
  simpa only [maximalMinor_ofOrderEmbedding] using h

/-- The square factor read from one selected target chart and the matching
source chart. -/
def chartFactor {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (target source : _root_.Matrix ι (Fin n) K) (rows : Fin n → ι) :
    _root_.Matrix (Fin n) (Fin n) K :=
  (target.submatrix rows id)⁻¹ * source.submatrix rows id

/-- Replacing one entry of the row tuple is the same as updating that row of
its selected square matrix. -/
theorem submatrix_update_rowTuple
    {n : ℕ} {ι : Type u} {R : Type v} [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (rows : Fin n → ι)
    (j : Fin n) (i : ι) :
    A.submatrix (Function.update rows j i) id =
      (A.submatrix rows id).updateRow j (A i) := by
  ext k l
  by_cases hkj : k = j
  · subst k
    simp
  · simp [hkj]

/-- Cramer's rule in the row convention: replacement determinants are the
selected determinant times the coordinates of the new row. -/
theorem det_smul_vecMul_nonsingInv_eq_updateRowDet
    {n : ℕ} {K : Type v} [Field K]
    (A : _root_.Matrix (Fin n) (Fin n) K) (r : Fin n → K)
    (hA : A.det ≠ 0) :
    A.det • (r ᵥ* A⁻¹) = fun j => (A.updateRow j r).det := by
  have hunit : IsUnit A.det := (isUnit_iff_ne_zero).2 hA
  funext j
  simpa only [Pi.smul_apply, _root_.Matrix.cramer_transpose_apply] using
    congrFun
      (_root_.Matrix.det_smul_inv_vecMul_eq_cramer_transpose A r hunit) j

/-- The selected target rows composed with the chart factor are exactly the
selected source rows. -/
theorem selectedSubmatrix_mul_chartFactor
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (target source : _root_.Matrix ι (Fin n) K) (rows : Fin n → ι)
    (htarget : orientedMaximalMinor target rows ≠ 0) :
    target.submatrix rows id * chartFactor target source rows =
      source.submatrix rows id := by
  have hdet : (target.submatrix rows id).det ≠ 0 := by
    simpa [orientedMaximalMinor] using htarget
  have hunit : IsUnit (target.submatrix rows id).det :=
    (isUnit_iff_ne_zero).2 hdet
  simp only [chartFactor]
  rw [← _root_.Matrix.mul_assoc,
    _root_.Matrix.mul_nonsing_inv _ hunit,
    _root_.Matrix.one_mul]

/-- The determinant of the chart factor is the proportionality scalar. -/
theorem det_chartFactor
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (target source : _root_.Matrix ι (Fin n) K) (rows : Fin n → ι)
    (scale : K)
    (htarget : orientedMaximalMinor target rows ≠ 0)
    (hbase : orientedMaximalMinor source rows =
      scale * orientedMaximalMinor target rows) :
    (chartFactor target source rows).det = scale := by
  have hmatrix := selectedSubmatrix_mul_chartFactor target source rows htarget
  have hdet := congrArg _root_.Matrix.det hmatrix
  rw [_root_.Matrix.det_mul] at hdet
  apply mul_left_cancel₀ htarget
  calc
    orientedMaximalMinor target rows * (chartFactor target source rows).det =
        orientedMaximalMinor source rows := by
      simpa [orientedMaximalMinor] using hdet
    _ = scale * orientedMaximalMinor target rows := hbase
    _ = orientedMaximalMinor target rows * scale := by ac_rfl

/-- Equality of all ordered maximal minors gives equality of the row
coordinates relative to the selected source and target charts. -/
theorem rowCoordinates_eq_of_orientedMaximalMinorsProportional
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (source target : _root_.Matrix ι (Fin n) K) (scale : K)
    (hscale : scale ≠ 0)
    (hminor : OrientedMaximalMinorsProportional source target scale)
    (rows : Fin n → ι)
    (htarget : orientedMaximalMinor target rows ≠ 0)
    (i : ι) :
    source i ᵥ* (source.submatrix rows id)⁻¹ =
      target i ᵥ* (target.submatrix rows id)⁻¹ := by
  let S : _root_.Matrix (Fin n) (Fin n) K := source.submatrix rows id
  let T : _root_.Matrix (Fin n) (Fin n) K := target.submatrix rows id
  have hbase : S.det = scale * T.det := by
    simpa [S, T, orientedMaximalMinor] using hminor rows
  have hT : T.det ≠ 0 := by
    simpa [T, orientedMaximalMinor] using htarget
  have hS : S.det ≠ 0 := by
    rw [hbase]
    exact mul_ne_zero hscale hT
  have hsource := det_smul_vecMul_nonsingInv_eq_updateRowDet S (source i) hS
  have htargetC := det_smul_vecMul_nonsingInv_eq_updateRowDet T (target i) hT
  funext j
  have hreplace := hminor (Function.update rows j i)
  have hrep : (S.updateRow j (source i)).det =
      scale * (T.updateRow j (target i)).det := by
    simpa [S, T, orientedMaximalMinor, submatrix_update_rowTuple] using hreplace
  have hleft : S.det * (source i ᵥ* S⁻¹) j =
      (S.updateRow j (source i)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hsource j
  have hright : T.det * (target i ᵥ* T⁻¹) j =
      (T.updateRow j (target i)).det := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun htargetC j
  apply mul_left_cancel₀ hS
  calc
    S.det * (source i ᵥ* S⁻¹) j =
        (S.updateRow j (source i)).det := hleft
    _ = scale * (T.updateRow j (target i)).det := hrep
    _ = scale * (T.det * (target i ᵥ* T⁻¹) j) := by rw [← hright]
    _ = (scale * T.det) * (target i ᵥ* T⁻¹) j := by ac_rfl
    _ = S.det * (target i ᵥ* T⁻¹) j := by rw [hbase]

/-- A nonzero proportionality scalar and one nonzero target chart force the
rectangular factorization `target * factor = source`. -/
theorem mul_chartFactor_eq_of_orientedMaximalMinorsProportional
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (source target : _root_.Matrix ι (Fin n) K) (scale : K)
    (hscale : scale ≠ 0)
    (hminor : OrientedMaximalMinorsProportional source target scale)
    (rows : Fin n → ι)
    (htarget : orientedMaximalMinor target rows ≠ 0) :
    target * chartFactor target source rows = source := by
  ext i j
  have hcoord := rowCoordinates_eq_of_orientedMaximalMinorsProportional
    source target scale hscale hminor rows htarget i
  have hsource : orientedMaximalMinor source rows ≠ 0 := by
    rw [hminor rows]
    exact mul_ne_zero hscale htarget
  have hsourceDet : (source.submatrix rows id).det ≠ 0 := by
    simpa [orientedMaximalMinor] using hsource
  have hsourceUnit : IsUnit (source.submatrix rows id).det :=
    (isUnit_iff_ne_zero).2 hsourceDet
  calc
    (target * chartFactor target source rows) i j =
        (target i ᵥ* chartFactor target source rows) j := rfl
    _ = ((target i ᵥ* (target.submatrix rows id)⁻¹) ᵥ*
          source.submatrix rows id) j := by
      rw [chartFactor, ← _root_.Matrix.vecMul_vecMul]
    _ = ((source i ᵥ* (source.submatrix rows id)⁻¹) ᵥ*
          source.submatrix rows id) j := by rw [hcoord]
    _ = (source i ᵥ*
          ((source.submatrix rows id)⁻¹ * source.submatrix rows id)) j := by
      rw [_root_.Matrix.vecMul_vecMul]
    _ = source i j := by
      rw [_root_.Matrix.nonsing_inv_mul _ hsourceUnit,
        _root_.Matrix.vecMul_one]

/-- The chart factor is the unique square matrix factoring `source` through a
rectangular `target` with a nonzero selected chart. -/
theorem chartFactor_unique
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (target source : _root_.Matrix ι (Fin n) K) (rows : Fin n → ι)
    (htarget : orientedMaximalMinor target rows ≠ 0)
    (L : _root_.Matrix (Fin n) (Fin n) K)
    (hL : target * L = source) :
    L = chartFactor target source rows := by
  have hdet : (target.submatrix rows id).det ≠ 0 := by
    simpa [orientedMaximalMinor] using htarget
  have hunit : IsUnit (target.submatrix rows id).det :=
    (isUnit_iff_ne_zero).2 hdet
  have hselected : target.submatrix rows id * L = source.submatrix rows id := by
    calc
      target.submatrix rows id * L = (target * L).submatrix rows id := by
        simpa using
          (_root_.Matrix.submatrix_mul target L rows id id Function.bijective_id).symm
      _ = source.submatrix rows id := by rw [hL]
  calc
    L = 1 * L := by rw [_root_.Matrix.one_mul]
    _ = ((target.submatrix rows id)⁻¹ * target.submatrix rows id) * L := by
      rw [_root_.Matrix.nonsing_inv_mul _ hunit]
    _ = (target.submatrix rows id)⁻¹ *
          (target.submatrix rows id * L) := by
      rw [_root_.Matrix.mul_assoc]
    _ = (target.submatrix rows id)⁻¹ * source.submatrix rows id := by
      rw [hselected]
    _ = chartFactor target source rows := rfl

/-- Combined existence, determinant, and uniqueness statement.  It includes
`n = 0`: then the oriented-minor hypothesis forces `scale = 1`. -/
theorem existsUnique_factor_of_orientedMaximalMinorsProportional
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (source target : _root_.Matrix ι (Fin n) K) (scale : K)
    (hscale : scale ≠ 0)
    (hminor : OrientedMaximalMinorsProportional source target scale)
    (rows : Fin n → ι)
    (htarget : orientedMaximalMinor target rows ≠ 0) :
    ∃! L : _root_.Matrix (Fin n) (Fin n) K,
      target * L = source ∧ L.det = scale := by
  refine ⟨chartFactor target source rows, ?_, ?_⟩
  · constructor
    · exact mul_chartFactor_eq_of_orientedMaximalMinorsProportional
        source target scale hscale hminor rows htarget
    · exact det_chartFactor target source rows scale htarget (hminor rows)
  · intro L hL
    exact chartFactor_unique target source rows htarget L hL.1

/-- A permutation of the ordered rows contributes its determinant sign. -/
theorem orientedMaximalMinor_permute
    {n : ℕ} {ι : Type u} {R : Type v} [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (rows : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) :
    orientedMaximalMinor A (rows ∘ σ) =
      (Equiv.Perm.sign σ : R) * orientedMaximalMinor A rows := by
  exact _root_.Matrix.det_permute σ (A.submatrix rows id)

/-- Noninjective row tuples give zero determinants, including repeated rows. -/
theorem orientedMaximalMinor_eq_zero_of_not_injective
    {n : ℕ} {ι : Type u} {R : Type v} [CommRing R]
    (A : _root_.Matrix ι (Fin n) R) (rows : Fin n → ι)
    (hrows : ¬ Function.Injective rows) : orientedMaximalMinor A rows = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hrows
  exact _root_.Matrix.det_zero_of_row_eq hne (by
    change A (rows i) = A (rows j)
    rw [hij])

/-- Sorting an injective tuple gives an increasing embedding and a permutation.
The proof also covers the unique tuple in dimension zero. -/
theorem exists_orderEmbedding_perm_of_injective
    {n : ℕ} {ι : Type u} [LinearOrder ι]
    (rows : Fin n → ι) (hrows : Function.Injective rows) :
    ∃ (sorted : Fin n ↪o ι) (σ : Equiv.Perm (Fin n)),
      rows = sorted ∘ σ := by
  classical
  let s : Finset ι := Finset.univ.image rows
  have hcard : s.card = n := by
    simpa [s] using Finset.card_image_of_injective Finset.univ hrows
  let e := s.orderIsoOfFin hcard
  let p : Fin n → Fin n := fun i => e.symm ⟨rows i, by simp [s]⟩
  have hp : ∀ i, s.orderEmbOfFin hcard (p i) = rows i := by
    intro i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨rows i, by simp [s]⟩)
  have hpinj : Function.Injective p := by
    intro i j hij
    apply hrows
    rw [← hp i, ← hp j, hij]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective p
    ((Finite.injective_iff_bijective).mp hpinj)
  refine ⟨s.orderEmbOfFin hcard, σ, ?_⟩
  funext i
  exact (hp i).symm

/-- Canonical increasing-row proportionality determines every ordered minor.
Both matrices use the same permutation sign; repeated rows vanish separately. -/
theorem orientedMaximalMinorsProportional_of_maximalMinorsProportional
    {n : ℕ} {ι : Type u} {R : Type v} [LinearOrder ι] [CommRing R]
    (source target : _root_.Matrix ι (Fin n) R) (scale : R)
    (hminor : MaximalMinorsProportional source target scale) :
    OrientedMaximalMinorsProportional source target scale := by
  classical
  intro rows
  by_cases hinj : Function.Injective rows
  · obtain ⟨sorted, σ, rfl⟩ := exists_orderEmbedding_perm_of_injective rows hinj
    rw [orientedMaximalMinor_permute, orientedMaximalMinor_permute,
      orientedMaximalMinor_eq_of_orderEmbedding source target scale hminor sorted]
    ring
  · rw [orientedMaximalMinor_eq_zero_of_not_injective source rows hinj,
      orientedMaximalMinor_eq_zero_of_not_injective target rows hinj, mul_zero]

/-- Empty determinants equal one, so the zero-dimensional scale equals one. -/
theorem scale_eq_one_of_orientedMaximalMinorsProportional_zero
    {ι : Type u} {R : Type v} [CommRing R]
    (source target : _root_.Matrix ι (Fin 0) R) (scale : R)
    (hminor : OrientedMaximalMinorsProportional source target scale) :
    scale = 1 := by
  have h := hminor Fin.elim0
  simpa [orientedMaximalMinor] using h.symm

/-- A nonzero chart and nonzero canonical minor scale recover the right factor. -/
theorem mul_chartFactor_eq_of_maximalMinorsProportional
    {n : ℕ} {ι : Type u} {K : Type v} [LinearOrder ι] [Field K]
    (source target : _root_.Matrix ι (Fin n) K) (scale : K)
    (hscale : scale ≠ 0) (hminor : MaximalMinorsProportional source target scale)
    (rows : Fin n → ι) (htarget : orientedMaximalMinor target rows ≠ 0) :
    target * chartFactor target source rows = source :=
  mul_chartFactor_eq_of_orientedMaximalMinorsProportional source target scale hscale
    (orientedMaximalMinorsProportional_of_maximalMinorsProportional
      source target scale hminor) rows htarget

/-- The recovered factor is a unit when its minor scale is nonzero. -/
theorem isUnit_chartFactor_of_scale_ne_zero
    {n : ℕ} {ι : Type u} {K : Type v} [Field K]
    (target source : _root_.Matrix ι (Fin n) K) (rows : Fin n → ι) (scale : K)
    (htarget : orientedMaximalMinor target rows ≠ 0) (hscale : scale ≠ 0)
    (hbase : orientedMaximalMinor source rows = scale * orientedMaximalMinor target rows) :
    IsUnit (chartFactor target source rows) := by
  apply (_root_.Matrix.isUnit_iff_isUnit_det _).mpr
  rw [det_chartFactor target source rows scale htarget hbase]
  exact isUnit_iff_ne_zero.mpr hscale

end Matrix
end MathlibAnnex
