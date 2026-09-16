import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic

/-!
# Smooth Piola identity in finite coordinate spaces

Hessian symmetry and antisymmetry of two-row replacement determinants give
the divergence-free cofactor identity. The compact-support divergence theorem
and a finite coordinate telescope then show that smooth compact perturbations
have determinant differences of integral zero.
-/

namespace MathlibAnnex
namespace Piola

/-- Matrix entries evaluated on standard coordinate vectors. -/
private noncomputable def stdMatrix {n N : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) : Matrix (Fin N) (Fin n) ℝ :=
  fun i j => A (Pi.single j 1) i

end Piola
end MathlibAnnex

/-!
# Cofactor identities

Cofactors are defined directly by determinant row replacement.  This avoids
adjugate transpose conventions and keeps every later identity in the same row
language as the determinant telescope.
-/

noncomputable section

open scoped BigOperators

namespace MathlibAnnex
namespace Piola

/-- Standard coordinate row. -/
def basisRow {n : ℕ} (j : Fin n) : (Fin n → ℝ) := Pi.single j 1

@[simp] theorem basisRow_apply {n : ℕ} (j q : Fin n) :
    basisRow j q = if q = j then 1 else 0 := by
  classical
  simp [basisRow, Pi.single_apply, eq_comm]

/-- Cofactor row, defined without choosing an adjugate convention. -/
def cofactorRow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : (Fin n → ℝ) :=
  fun j => (A.updateRow i (basisRow j)).det

/-- Matrix with two designated rows replaced by coordinate rows. -/
def twoRowReplacement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i k j q : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  (A.updateRow i (basisRow j)).updateRow k (basisRow q)

/-- Divergence in the coordinate basis consumed by Mathlib's box theorem. -/
def coordinateDivergence {m : ℕ}
    (F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (x : (Fin (m + 1) → ℝ)) : ℝ :=
  ∑ i, fderiv ℝ F x (Pi.single i 1) i

end Piola
end MathlibAnnex


/-!
# Cofactor identities
-/

noncomputable section

open scoped BigOperators

namespace MathlibAnnex
namespace Piola

/-- Coordinate-basis expansion of a row vector. -/
theorem sum_smul_basisRow {n : ℕ} (v : (Fin n → ℝ)) :
    (∑ j, v j • basisRow j) = v := by
  classical
  ext q
  simp [basisRow, Pi.single_apply]

/-- Determinant is linear in one updated row over a finite sum. -/
theorem det_updateRow_finset_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (s : Finset (Fin n)) (v : Fin n → (Fin n → ℝ)) :
    (A.updateRow i (s.sum v)).det =
      s.sum (fun j => (A.updateRow i (v j)).det) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Matrix.det_updateRow_add, ih, Finset.sum_insert hj]

/-- Expansion along the updated row in the row-replacement cofactor convention. -/
theorem det_updateRow_eq_sum_mul_cofactorRow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (v : (Fin n → ℝ)) :
    (A.updateRow i v).det = ∑ j, v j * cofactorRow A i j := by
  classical
  calc
    (A.updateRow i v).det =
        (A.updateRow i (∑ j, v j • basisRow j)).det := by
      rw [sum_smul_basisRow]
    _ = ∑ j, (A.updateRow i (v j • basisRow j)).det := by
      simpa using
        (det_updateRow_finset_sum A i Finset.univ
          (fun j => v j • basisRow j))
    _ = ∑ j, v j * cofactorRow A i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.det_updateRow_smul]
      rfl

end Piola
end MathlibAnnex


/-!
# Cofactor identities

The completed field definition is isolated from the differential Piola proof so
that it remains an independent node of the existing import DAG.
-/

noncomputable section

namespace MathlibAnnex
namespace Piola

/-- Cofactor row field of the derivative of a smooth square map. -/
def cofactorRowField {n : ℕ} (H : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x => cofactorRow (stdMatrix (fderiv ℝ H x)) i

end Piola
end MathlibAnnex


/-!
# Cofactor identities

This packet is purely finite-dimensional algebra.  It does not import
calculus, integration, or compact-support machinery.
-/

noncomputable section

open scoped BigOperators

namespace MathlibAnnex
namespace Piola

/-- Exchanging the two replacement rows negates the determinant. -/
theorem det_twoRowReplacement_swap {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i k j q : Fin n) (hik : i ≠ k) :
    (twoRowReplacement A i k j q).det =
      -(twoRowReplacement A i k q j).det := by
  classical
  have hswap :
      twoRowReplacement A i k q j ∘ Equiv.swap i k =
        twoRowReplacement A i k j q := by
    funext r
    by_cases hri : r = i
    · subst r
      simp [twoRowReplacement, Function.comp_apply, hik]
    · by_cases hrk : r = k
      · subst r
        simp [twoRowReplacement, Function.comp_apply, hik]
      · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hri hrk]
        simp [twoRowReplacement, hri, hrk]
  change (Matrix.detRowAlternating
      (R := ℝ) (n := Fin n)) (twoRowReplacement A i k j q) =
        -(Matrix.detRowAlternating
          (R := ℝ) (n := Fin n)) (twoRowReplacement A i k q j)
  calc
    (Matrix.detRowAlternating
        (R := ℝ) (n := Fin n)) (twoRowReplacement A i k j q) =
        (Matrix.detRowAlternating
          (R := ℝ) (n := Fin n))
            (twoRowReplacement A i k q j ∘ Equiv.swap i k) := by
      rw [hswap]
    _ = -(Matrix.detRowAlternating
        (R := ℝ) (n := Fin n)) (twoRowReplacement A i k q j) :=
      (Matrix.detRowAlternating
        (R := ℝ) (n := Fin n)).map_swap
          (twoRowReplacement A i k q j) hik

/-- A symmetric coefficient matrix contracted with an antisymmetric matrix has
zero finite double sum. -/
theorem sum_symmetric_mul_antisymmetric_eq_zero
    {ι : Type*} [Fintype ι]
    (B D : ι → ι → ℝ)
    (hB : ∀ i j, B i j = B j i)
    (hD : ∀ i j, D i j = -D j i) :
    (∑ i, ∑ j, B i j * D i j) = 0 := by
  have hneg : (∑ i, ∑ j, B i j * D i j) =
      -(∑ i, ∑ j, B i j * D i j) := by
    calc
      (∑ i, ∑ j, B i j * D i j) =
          ∑ i, ∑ j, B j i * D j i := by
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, -(B i j * D i j) := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        rw [hB j i, hD j i]
        ring
      _ = -(∑ i, ∑ j, B i j * D i j) := by
        simp only [Finset.sum_neg_distrib]
  linarith

/-- Algebraic cancellation form used after Hessian symmetry is exposed. -/
theorem sum_hessian_twoRowReplacement_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) (hik : i ≠ k)
    (B : Fin n → Fin n → ℝ) (hB : ∀ j q, B j q = B q j) :
    (∑ j, ∑ q, B j q * (twoRowReplacement A i k j q).det) = 0 := by
  apply sum_symmetric_mul_antisymmetric_eq_zero B
    (fun j q => (twoRowReplacement A i k j q).det) hB
  intro j q
  exact det_twoRowReplacement_swap A i k j q hik

end Piola
end MathlibAnnex


/-!
# Cofactor identities

This module separates the already available symmetry of the second derivative
and the already compiled two-row determinant alternation from the remaining
calculus expansion of the cofactor derivative.
-/

noncomputable section

open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

/-- One scalar coordinate of the second Fréchet derivative. -/
def hessianCoordinate {n : ℕ} (H : (Fin n → ℝ) → (Fin n → ℝ))
    (x : (Fin n → ℝ)) (k j q : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ H) x (basisRow j) (basisRow q) k

/-- Coordinate Hessian coefficients are symmetric in their two input rows. -/
theorem hessianCoordinate_comm {n : ℕ} {H : (Fin n → ℝ) → (Fin n → ℝ)}
    (hH : ContDiff ℝ 2 H) (x : (Fin n → ℝ)) (k j q : Fin n) :
    hessianCoordinate H x k j q = hessianCoordinate H x k q j :=
 by
  have hsymm : IsSymmSndFDerivAt ℝ H x :=
    hH.contDiffAt.isSymmSndFDerivAt (by norm_num)
  unfold hessianCoordinate
  exact congrArg (fun y : (Fin n → ℝ) => y k)
    (hsymm (basisRow j) (basisRow q))

/-- The scalar Hessian coefficients cancel against an antisymmetric pair of
replacement rows. -/
theorem sum_hessianCoordinate_twoRowReplacement_eq_zero
    {n : ℕ} {H : (Fin n → ℝ) → (Fin n → ℝ)}
    (hH : ContDiff ℝ 2 H) (x : (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (i k : Fin n) (hik : i ≠ k) :
    (∑ j, ∑ q,
      hessianCoordinate H x k j q *
        (twoRowReplacement A i k j q).det) = 0 :=
 by
  apply sum_hessian_twoRowReplacement_eq_zero A i k hik
  intro j q
  exact hessianCoordinate_comm hH x k j q

/-- Once the derivative of the cofactor row is expanded into its rowwise
Hessian formula, Piola cancellation follows from the preceding finite lemma. -/
theorem piola_divergence_eq_zero_of_expansion
    {n : ℕ} {H : (Fin n → ℝ) → (Fin n → ℝ)}
    (hH : ContDiff ℝ 2 H) (i : Fin n) (x : (Fin n → ℝ))
    (hexpand :
      (∑ j, fderiv ℝ (cofactorRowField H i) x
        (Pi.single j 1) j) =
        ∑ k ∈ Finset.univ.erase i, ∑ j, ∑ q,
          hessianCoordinate H x k j q *
            (twoRowReplacement
              (stdMatrix (fderiv ℝ H x)) i k j q).det) :
    ∑ j, fderiv ℝ (cofactorRowField H i) x
      (Pi.single j 1) j = 0 :=
 by
  rw [hexpand]
  apply Finset.sum_eq_zero
  intro k hk
  have hik : i ≠ k := (Finset.mem_erase.mp hk).1.symm
  exact sum_hessianCoordinate_twoRowReplacement_eq_zero
    hH x (stdMatrix (fderiv ℝ H x)) i k hik

end Piola
end MathlibAnnex


/-!
# Cofactor identities

Hessian symmetry and the finite antisymmetric cancellation are now isolated in
`PiolaHessian`. This module has one remaining obligation: expose the derivative
of the cofactor determinant as the exact rowwise Hessian sum.
-/

noncomputable section

open Set
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

/-- The cofactor row field has zero divergence (Piola identity). -/
theorem divergence_cofactorRowField_eq_zero
    {n : ℕ} {H : (Fin n → ℝ) → (Fin n → ℝ)}
    (hH : ContDiff ℝ 2 H) (i : Fin n) (x : (Fin n → ℝ)) :
    ∑ j, fderiv ℝ (cofactorRowField H i) x (Pi.single j 1) j = 0 :=
 by
  apply piola_divergence_eq_zero_of_expansion hH i x
  classical
  have hdf : DifferentiableAt ℝ (fderiv ℝ H) x := by
    fun_prop
  change (∑ j, fderiv ℝ
    (fun y r => ((stdMatrix (fderiv ℝ H y)).updateRow i
      (basisRow r)).det) x (Pi.single j 1) j) = _
  simp only [hessianCoordinate,
    twoRowReplacement, Matrix.det_apply]
  have hprod (r : Fin n) (σ : Equiv.Perm (Fin n)) :
      HasFDerivAt
        (fun y => ∏ k,
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k)
        (∑ k,
          (∏ l ∈ Finset.univ.erase k,
            (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l) •
          fderiv ℝ (fun y =>
            (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x) x := by
    apply HasFDerivAt.finsetProd
    intro k hk
    by_cases hki : σ k = i
    · simpa [Matrix.updateRow_apply, hki] using
        (differentiableAt_const (c := basisRow r k)).hasFDerivAt
    · exact (by
        simp only [Matrix.updateRow_apply, hki, ↓reduceIte, stdMatrix]
        fun_prop : DifferentiableAt ℝ (fun y =>
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x).hasFDerivAt
  have hscalar (r : Fin n) :
      HasFDerivAt
        (fun y => ∑ σ, Equiv.Perm.sign σ • ∏ k,
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k)
        (∑ σ, Equiv.Perm.sign σ •
          (∑ k,
            (∏ l ∈ Finset.univ.erase k,
              (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l) •
            fderiv ℝ (fun y =>
              (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x)) x := by
    have hs : HasFDerivAt
        (∑ σ, Equiv.Perm.sign σ • (fun y : (Fin n → ℝ) => ∏ k,
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k))
        (∑ σ, Equiv.Perm.sign σ •
          (∑ k,
            (∏ l ∈ Finset.univ.erase k,
              (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l) •
            fderiv ℝ (fun y =>
              (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x)) x :=
      HasFDerivAt.sum (u := Finset.univ) (fun σ _ =>
        (hprod r σ).const_smul (Equiv.Perm.sign σ))
    have hfun :
        (∑ σ, Equiv.Perm.sign σ • (fun y : (Fin n → ℝ) => ∏ k,
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k)) =
        (fun y => ∑ σ, Equiv.Perm.sign σ • ∏ k,
          (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply]
    rw [hfun] at hs
    exact hs
  have hentry (r : Fin n) (σ : Equiv.Perm (Fin n)) (k : Fin n) :
      fderiv ℝ (fun y =>
        (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x
          (Pi.single r 1) =
        if σ k = i then 0 else
          (fderiv ℝ (fderiv ℝ H) x) (basisRow r) (basisRow k) (σ k) := by
    change fderiv ℝ (fun y =>
      (stdMatrix (fderiv ℝ H y)).updateRow i (basisRow r) (σ k) k) x
        (basisRow r) = _
    by_cases hki : σ k = i
    · simp [Matrix.updateRow_apply, hki]
    · simp only [Matrix.updateRow_apply, hki, ↓reduceIte, stdMatrix]
      calc
        fderiv ℝ (fun y => (fderiv ℝ H y) (basisRow k) (σ k)) x
            (basisRow r) =
            (fderiv ℝ (fun y => (fderiv ℝ H y) (basisRow k)) x)
              (basisRow r) (σ k) := by
          have hp := fderiv_pi (x := x)
            (φ := fun a y => (fderiv ℝ H y) (basisRow k) a)
            (fun a => show DifferentiableAt ℝ
              (fun y => (fderiv ℝ H y) (basisRow k) a) x from by fun_prop)
          exact (congrArg (fun L => L (basisRow r) (σ k)) hp).symm
        _ = (fderiv ℝ (fderiv ℝ H) x) (basisRow r) (basisRow k) (σ k) := by
          rw [fderiv_clm_apply hdf (differentiableAt_const (c := basisRow k))]
          simp
  have hdetprod (r K q : Fin n) (σ : Equiv.Perm (Fin n)) :
      (∏ l, ((stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r)).updateRow
        K (basisRow q) (σ l) l) =
        if σ q = K then
          ∏ l ∈ Finset.univ.erase q,
            (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l
        else 0 := by
    by_cases hq : σ q = K
    · subst K
      rw [← Finset.prod_erase_mul Finset.univ
        (fun l => ((stdMatrix (fderiv ℝ H x)).updateRow i
          (basisRow r)).updateRow (σ q) (basisRow q) (σ l) l)
        (Finset.mem_univ q)]
      simp only [Matrix.updateRow_apply, basisRow_apply, σ.injective.eq_iff,
        if_pos]
      rw [mul_one]
      apply Finset.prod_congr rfl
      intro l hl
      have hlq : l ≠ q := (Finset.mem_erase.mp hl).1
      simp [hlq]
    · rw [if_neg hq]
      apply Finset.prod_eq_zero (Finset.mem_univ (σ.symm K))
      have hne : σ.symm K ≠ q := by
        intro heq
        apply hq
        rw [← heq, σ.apply_symm_apply]
      simp [Matrix.updateRow_apply, basisRow_apply, hne]
  rw [fderiv_pi (fun r => (hscalar r).differentiableAt)]
  simp only [ContinuousLinearMap.pi_apply]
  simp_rw [(hscalar _).fderiv]
  simp only [_root_.sum_apply, smul_apply]
  simp_rw [hentry]
  simp_rw [hdetprod]
  have hsumK (r q : Fin n) (σ : Equiv.Perm (Fin n)) :
      (∑ K ∈ Finset.univ.erase i,
        ((fderiv ℝ (fderiv ℝ H) x) (basisRow r)) (basisRow q) K *
          (Equiv.Perm.sign σ •
            if σ q = K then
              ∏ l ∈ Finset.univ.erase q,
                (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l
            else 0)) =
        Equiv.Perm.sign σ •
          ((∏ l ∈ Finset.univ.erase q,
              (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l) *
            if σ q = i then 0 else
              ((fderiv ℝ (fderiv ℝ H) x) (basisRow r)) (basisRow q) (σ q)) := by
    by_cases hqi : σ q = i
    · rw [if_pos hqi]
      simp only [mul_zero, smul_zero]
      apply Finset.sum_eq_zero
      intro K hK
      have hKi : K ≠ i := (Finset.mem_erase.mp hK).1
      simp only [hqi]
      rw [if_neg hKi.symm]
      simp
    · rw [if_neg hqi]
      rw [Finset.sum_eq_single (σ q)]
      · simp only [if_pos, mul_comm]
        rw [smul_mul_assoc]
      · intro K hK hKq
        simp [hKq.symm]
      · intro hmem
        exact (hmem (Finset.mem_erase.mpr ⟨hqi, Finset.mem_univ _⟩)).elim
  simp_rw [Finset.smul_sum, Finset.mul_sum]
  let T : Fin n → Fin n → Fin n → Equiv.Perm (Fin n) → ℝ :=
    fun K r q σ =>
      ((fderiv ℝ (fderiv ℝ H) x) (basisRow r)) (basisRow q) K *
        (Equiv.Perm.sign σ •
          if σ q = K then
            ∏ l ∈ Finset.univ.erase q,
              (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l
          else 0)
  have hreorder :
      (∑ K ∈ Finset.univ.erase i, ∑ r, ∑ q, ∑ σ, T K r q σ) =
        ∑ r, ∑ σ, ∑ q, ∑ K ∈ Finset.univ.erase i, T K r q σ := by
    calc
      (∑ K ∈ Finset.univ.erase i, ∑ r, ∑ q, ∑ σ, T K r q σ) =
          ∑ K ∈ Finset.univ.erase i, ∑ r, ∑ σ, ∑ q, T K r q σ := by
        apply Finset.sum_congr rfl
        intro K hK
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _ = ∑ r, ∑ K ∈ Finset.univ.erase i, ∑ σ, ∑ q, T K r q σ := by
        exact Finset.sum_comm
      _ = ∑ r, ∑ σ, ∑ K ∈ Finset.univ.erase i, ∑ q, T K r q σ := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _ = ∑ r, ∑ σ, ∑ q, ∑ K ∈ Finset.univ.erase i, T K r q σ := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro σ hσ
        exact Finset.sum_comm
  change _ = ∑ K ∈ Finset.univ.erase i, ∑ r, ∑ q, ∑ σ, T K r q σ
  rw [hreorder]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro q hq
  change Equiv.Perm.sign σ •
      ((∏ l ∈ Finset.univ.erase q,
          (stdMatrix (fderiv ℝ H x)).updateRow i (basisRow r) (σ l) l) •
        if σ q = i then 0 else
          ((fderiv ℝ (fderiv ℝ H) x) (basisRow r)) (basisRow q) (σ q)) = _
  simpa only [smul_eq_mul] using (hsumK r q σ).symm
end Piola
end MathlibAnnex


noncomputable section

open Set
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

def singleOutputPerturb {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (i : Fin n) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x => g x + φ x • basisRow i

def componentFlux {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (i : Fin n) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x => φ x • cofactorRowField g i x

def outputHybrid {n : ℕ} (g u : (Fin n → ℝ) → (Fin n → ℝ))
    (s : Finset (Fin n)) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x i => g x i + if i ∈ s then u x i else 0

@[simp] theorem outputHybrid_empty {n : ℕ} (g u : (Fin n → ℝ) → (Fin n → ℝ)) :
    outputHybrid g u ∅ = g := by
  funext x i
  simp [outputHybrid]

@[simp] theorem outputHybrid_univ {n : ℕ} (g u : (Fin n → ℝ) → (Fin n → ℝ)) :
    outputHybrid g u Finset.univ = fun x => g x + u x := by
  funext x i
  simp [outputHybrid]

end Piola
end MathlibAnnex

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

theorem coordinateDivergence_eq_zero_of_not_mem_tsupport
    {m : ℕ} {F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    {x : (Fin (m + 1) → ℝ)} (hx : x ∉ tsupport F) :
    coordinateDivergence F x = 0 := by
  have hderiv : fderiv ℝ F x = 0 :=
    fderiv_of_notMem_tsupport ℝ hx
  simp [coordinateDivergence, hderiv]

theorem exists_open_box_containing_compact
    {m : ℕ} {K : Set ((Fin (m + 1) → ℝ))} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧
      K ⊆ Set.pi Set.univ
        (fun _ : Fin (m + 1) => Set.Ioo (-R) R) := by
  rcases hK.isBounded.subset_closedBall 0 with ⟨R, hR⟩
  refine' ⟨max R 0 + 1, _, _⟩
  · have hmax0 : 0 ≤ max R 0 := le_max_right R 0
    linarith
  · intro x hx
    have hxR := hR hx
    have hnorm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxR
    have hRmax : R ≤ max R 0 := le_max_left R 0
    apply Set.mem_univ_pi.mpr
    intro i
    have hcoord : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    constructor
    · have hlow : -‖x‖ ≤ x i := neg_le_of_abs_le hcoord
      linarith
    · have hupp : x i ≤ ‖x‖ :=
        le_trans (le_abs_self (x i)) hcoord
      linarith

end Piola
end MathlibAnnex

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

theorem integral_coordinateDivergence_eq_zero_of_contDiff_hasCompactSupport
    {m : ℕ} {F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∫ x, coordinateDivergence F x = 0 :=
 by
  rcases exists_open_box_containing_compact hFc.isCompact with
    ⟨R, hR, hbox⟩
  let a : (Fin (m + 1) → ℝ) := fun _ => -R
  let b : (Fin (m + 1) → ℝ) := fun _ => R
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    linarith
  have hsupp : Function.support F ⊆
      Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) := by
    intro x hx
    simpa [a, b] using hbox (subset_tsupport _ hx)
  have houtside : ∀ x ∉ Set.Icc a b, coordinateDivergence F x = 0 := by
    intro x hx
    apply coordinateDivergence_eq_zero_of_not_mem_tsupport
    intro hxt
    have hcoord : ∀ j, a j < x j ∧ x j < b j := by
      intro j
      simpa [a, b] using (Set.mem_univ_pi.mp (hbox hxt) j)
    apply hx
    exact ⟨fun j => (hcoord j).1.le, fun j => (hcoord j).2.le⟩

  have hdivcont : Continuous (coordinateDivergence F) := by
    unfold coordinateDivergence
    fun_prop
  have hbox := integral_divergence_of_hasFDerivAt_off_countable
    a b hab F (fun x => fderiv ℝ F x) ∅ (by simp)
    hF.continuous.continuousOn
    (by
      intro x hx
      exact ((hF.differentiable (by norm_num)) x).hasFDerivAt)
    (by
      exact hdivcont.integrableOn_Icc)
  have hfront : ∀ (i : Fin (m + 1)) (y : Fin m → ℝ),
      F (i.insertNth (b i) y) i = 0 := by
    intro i y
    by_contra hne
    have hmem : i.insertNth (b i) y ∈ Function.support F := by
      intro hz
      exact hne (congrFun hz i)
    have hi := (Set.mem_univ_pi.mp (hsupp hmem)) i
    simpa using hi.2
  have hback : ∀ (i : Fin (m + 1)) (y : Fin m → ℝ),
      F (i.insertNth (a i) y) i = 0 := by
    intro i y
    by_contra hne
    have hmem : i.insertNth (a i) y ∈ Function.support F := by
      intro hz
      exact hne (congrFun hz i)
    have hi := (Set.mem_univ_pi.mp (hsupp hmem)) i
    simpa using hi.1
  have hboxzero : ∫ x in Set.Icc a b, coordinateDivergence F x = 0 := by
    simpa only [coordinateDivergence, hfront, hback, integral_zero,
      sub_self, Finset.sum_const_zero] using hbox
  calc
    (∫ x, coordinateDivergence F x) =
        ∫ x in Set.Icc a b, coordinateDivergence F x := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with x hx
      exact houtside x hx
    _ = 0 := hboxzero

end Piola
end MathlibAnnex

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

theorem support_componentFlux_subset {n : ℕ}
    (g : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) (i : Fin n) :
    Function.support (componentFlux g φ i) ⊆ Function.support φ :=
 by
  intro x hx hφ
  apply hx
  simp [componentFlux, hφ]

theorem componentFlux_hasCompactSupport {n : ℕ}
    {g : (Fin n → ℝ) → (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ} {i : Fin n}
    (hφc : HasCompactSupport φ) :
    HasCompactSupport (componentFlux g φ i) :=
 by

  have hs := support_componentFlux_subset g φ i
  unfold HasCompactSupport at hφc ⊢
  exact hφc.of_isClosed_subset isClosed_closure (closure_mono hs)

theorem divergence_componentFlux_eq_det_sub
    {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
    (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (i : Fin n) (x : (Fin n → ℝ)) :
    ∑ j, fderiv ℝ (componentFlux g φ i) x (Pi.single j 1) j =
      LinearMap.det ((fderiv ℝ (singleOutputPerturb g φ i) x).toLinearMap) -
        LinearMap.det ((fderiv ℝ g x).toLinearMap) :=
 by
  have hpiola := divergence_cofactorRowField_eq_zero hg i x
  have hcofactor := det_updateRow_eq_sum_mul_cofactorRow
    (stdMatrix (fderiv ℝ g x)) i
    (fun j => fderiv ℝ φ x (Pi.single j 1))

  have hφd : DifferentiableAt ℝ φ x :=
    (hφ.differentiable (by norm_num)) x
  have hgd : DifferentiableAt ℝ g x :=
    (hg.differentiable (by norm_num)) x
  have hcofsmooth : ContDiff ℝ 1 (cofactorRowField g i) := by
    have hdg : ContDiff ℝ 1 (fderiv ℝ g) :=
      hg.fderiv_right (by norm_num)
    unfold cofactorRowField cofactorRow
    rw [contDiff_pi]
    intro q
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ hσ
    apply contDiff_const.mul
    apply contDiff_prod
    intro k hk
    by_cases hki : σ k = i
    · simp only [Matrix.updateRow_apply, hki, if_true]
      fun_prop
    · simp only [Matrix.updateRow_apply, hki, if_false]
      unfold stdMatrix
      fun_prop
  have hcofd : DifferentiableAt ℝ (cofactorRowField g i) x :=
    (hcofsmooth.differentiable (by norm_num)) x
  have hsingle :
      fderiv ℝ (singleOutputPerturb g φ i) x =
        fderiv ℝ g x + (fderiv ℝ φ x).smulRight (basisRow i) := by
    unfold singleOutputPerturb
    exact (hgd.hasFDerivAt.add
      (hφd.hasFDerivAt.smul_const (basisRow i))).fderiv
  have hmat :
      stdMatrix (fderiv ℝ (singleOutputPerturb g φ i) x) =
        (stdMatrix (fderiv ℝ g x)).updateRow i
          ((stdMatrix (fderiv ℝ g x)) i +
            fun j => fderiv ℝ φ x (Pi.single j 1)) := by
    rw [hsingle]
    ext r c
    by_cases hri : r = i
    · subst r
      simp [stdMatrix, basisRow]
    · simp [stdMatrix, basisRow, hri]
  unfold componentFlux
  rw [fderiv_fun_smul hφd hcofd]
  change (∑ j, (φ x *
      fderiv ℝ (cofactorRowField g i) x (Pi.single j 1) j +
      fderiv ℝ φ x (Pi.single j 1) *
        cofactorRow (stdMatrix (fderiv ℝ g x)) i j)) = _
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hpiola, mul_zero, zero_add]
  rw [← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix']
  change _ = (stdMatrix (fderiv ℝ (singleOutputPerturb g φ i) x)).det -
    (stdMatrix (fderiv ℝ g x)).det
  rw [hmat, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, hcofactor]
  ring

end Piola
end MathlibAnnex

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

theorem integral_det_singleOutputPerturb_sub_eq_zero
    {m : ℕ} {g : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    {φ : (Fin (m + 1) → ℝ) → ℝ}
    (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (i : Fin (m + 1)) :
    ∫ x, (LinearMap.det ((fderiv ℝ (singleOutputPerturb g φ i) x).toLinearMap) -
      LinearMap.det ((fderiv ℝ g x).toLinearMap)) = 0 :=
 by
  have hfluxc : HasCompactSupport (componentFlux g φ i) :=
    componentFlux_hasCompactSupport hφc
  have hfluxsmooth : ContDiff ℝ 1 (componentFlux g φ i) := by

    have hdg : ContDiff ℝ 1 (fderiv ℝ g) :=
      hg.fderiv_right (by norm_num)
    have hcofsmooth : ContDiff ℝ 1 (cofactorRowField g i) := by
      unfold cofactorRowField cofactorRow
      rw [contDiff_pi]
      intro q
      simp only [Matrix.det_apply']
      apply ContDiff.sum
      intro σ hσ
      apply contDiff_const.mul
      apply contDiff_prod
      intro k hk
      by_cases hki : σ k = i
      · simp only [Matrix.updateRow_apply, hki, if_true]
        fun_prop
      · simp only [Matrix.updateRow_apply, hki, if_false]
        unfold stdMatrix
        fun_prop
    unfold componentFlux
    exact hφ.smul hcofsmooth
  have hdiv :=
    integral_coordinateDivergence_eq_zero_of_contDiff_hasCompactSupport
      hfluxsmooth hfluxc

  simpa only [coordinateDivergence,
    divergence_componentFlux_eq_det_sub hg hφ i] using hdiv

end Piola
end MathlibAnnex

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace MathlibAnnex
namespace Piola

theorem outputHybrid_insert_eq_singleOutputPerturb
    {n : ℕ} (g u : (Fin n → ℝ) → (Fin n → ℝ)) (s : Finset (Fin n))
    (i : Fin n) (hi : i ∉ s) :
    outputHybrid g u (insert i s) =
      singleOutputPerturb (outputHybrid g u s) (fun x => u x i) i :=
 by
  funext x j
  by_cases hji : j = i
  · subst j
    simp [outputHybrid, singleOutputPerturb, basisRow, hi]
  · simp [outputHybrid, singleOutputPerturb, basisRow, hji]

theorem integral_det_fderiv_add_sub_eq_zero_of_contDiff
    {m : ℕ} {g u : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (huc : HasCompactSupport u) :
    ∫ x, (LinearMap.det ((fderiv ℝ (fun y => g y + u y) x).toLinearMap) -
      LinearMap.det ((fderiv ℝ g x).toLinearMap)) = 0 :=
 by

  have hcomponent : ∀ i : Fin (m + 1),
      HasCompactSupport (fun x => u x i) := by
    intro i

    have hs : Function.support (fun x => u x i) ⊆ Function.support u := by
      intro x hx hux
      exact hx (congrFun hux i)
    unfold HasCompactSupport at huc ⊢
    exact huc.of_isClosed_subset isClosed_closure (closure_mono hs)
  have hhybrid : ∀ s : Finset (Fin (m + 1)),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (outputHybrid g u s) := by
    intro s
    unfold outputHybrid
    rw [contDiff_pi]
    intro i
    by_cases hi : i ∈ s
    · simp only [hi, if_true]
      fun_prop
    · simp only [hi, if_false, add_zero]
      fun_prop
  have hcoord : ∀ i : Fin (m + 1),
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => u x i) := by
    intro i
    fun_prop
  have hstepIntegrable : ∀ (G : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)),
      ContDiff ℝ (↑(⊤ : ℕ∞)) G → ∀ i : Fin (m + 1),
      Integrable (fun x =>
        LinearMap.det ((fderiv ℝ (singleOutputPerturb G (fun y => u y i) i) x).toLinearMap) -
          LinearMap.det ((fderiv ℝ G x).toLinearMap)) := by
    intro G hG i
    let q := fun x =>
      LinearMap.det ((fderiv ℝ (singleOutputPerturb G (fun y => u y i) i) x).toLinearMap) -
        LinearMap.det ((fderiv ℝ G x).toLinearMap)
    have hpert : ContDiff ℝ (↑(⊤ : ℕ∞))
        (singleOutputPerturb G (fun y => u y i) i) := by
      unfold singleOutputPerturb
      fun_prop
    have hqcont : Continuous q := by
      exact (ContinuousLinearMap.continuous_det.comp
        (hpert.continuous_fderiv (by simp))).sub
          (ContinuousLinearMap.continuous_det.comp (hG.continuous_fderiv (by simp)))
    have hqsupp : Function.support q ⊆ tsupport (fun y => u y i) := by
      intro x hx
      by_contra hxout
      apply hx
      have hdu : fderiv ℝ (fun y => u y i) x = 0 :=
        fderiv_of_notMem_tsupport ℝ hxout
      have hGd : DifferentiableAt ℝ G x :=
        ((hG.differentiable (by simp)) x)
      have hud : DifferentiableAt ℝ (fun y => u y i) x :=
        ((hcoord i).differentiable (by simp)) x
      have hd :
          fderiv ℝ (singleOutputPerturb G (fun y => u y i) i) x =
            fderiv ℝ G x +
              (fderiv ℝ (fun y => u y i) x).smulRight (basisRow i) := by
        unfold singleOutputPerturb
        exact (hGd.hasFDerivAt.add
          (hud.hasFDerivAt.smul_const (basisRow i))).fderiv
      simp [q, hd, hdu]
    have hqcompact : HasCompactSupport q := by
      unfold HasCompactSupport
      exact (hcomponent i).of_isClosed_subset isClosed_closure
        (closure_minimal hqsupp isClosed_closure)
    exact hqcont.integrable_of_hasCompactSupport hqcompact
  let q := fun (s : Finset (Fin (m + 1))) x =>
    LinearMap.det ((fderiv ℝ (outputHybrid g u s) x).toLinearMap) -
      LinearMap.det ((fderiv ℝ g x).toLinearMap)
  have htel : ∀ s : Finset (Fin (m + 1)),
      Integrable (q s) ∧ ∫ x, q s x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [q]
    | @insert i s hi ih =>
        have hone := integral_det_singleOutputPerturb_sub_eq_zero
          ((hhybrid s).of_le (by
            exact WithTop.coe_le_coe.mpr
              (show (2 : ℕ∞) ≤ ⊤ from le_top)))
          ((hcoord i).of_le (by norm_num)) (hcomponent i) i
        rw [← outputHybrid_insert_eq_singleOutputPerturb g u s i hi] at hone
        have hstep := hstepIntegrable (outputHybrid g u s) (hhybrid s) i
        rw [← outputHybrid_insert_eq_singleOutputPerturb g u s i hi] at hstep
        have hsplit : q (insert i s) = fun x =>
            (LinearMap.det ((fderiv ℝ (outputHybrid g u (insert i s)) x).toLinearMap) -
              LinearMap.det ((fderiv ℝ (outputHybrid g u s) x).toLinearMap)) + q s x := by
          funext x
          simp only [q]
          ring
        rw [hsplit]
        constructor
        · exact hstep.add ih.1
        · rw [integral_add hstep ih.1, hone, ih.2, add_zero]
  simpa [q] using (htel Finset.univ).2

end Piola
end MathlibAnnex
