import MathlibAnnex.Analysis.Normed.Sequence.FunctionalAttainment
import MathlibAnnex.Analysis.CStarAlgebra.Matrix.CornerMaps
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Util.Superscript

/-!
# Every bounded functional as an actual matrix coefficient

For f ≠ 0, extend f to bounded sequences and choose a contraction x with
f_seq(x)=‖f‖.  Dilate x to a unitary U in M₂(l∞(A)).  The functional
    phi(M) = f_seq((U*M)₀₁) / ‖f‖
has norm at most one and phi(1)=1, hence is a genuine state.  In its GNS space,
restrict along a ↦ diag(const a,const a).  The vectors pi(U)Ω and pi(e₀₁)Ω have
norm at most one and recover f/‖f‖.  This does not use a polar decomposition of
f, a C*-structure on A**, general bilinear weak compactness, or an invariant mean.
The construction uses C01 helpers read-only; no source-author-A file is modified.
C03 proof bodies, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

namespace MathlibAnnex.FunctionalCoefficient
open MathlibAnnex.MatrixContraction
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

local instance sequenceOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _
local instance sequenceStarOrder : StarOrderedRing (ℕ →ᵇ A) :=
  CStarAlgebra.spectralOrderedRing _

abbrev AuxiliaryMatrixAlgebra (A : Type u) [CStarAlgebra A] := TwoByTwo (ℕ →ᵇ A)

local instance sequenceNontrivial : Nontrivial (ℕ →ᵇ A) := by
  refine ⟨⟨BoundedContinuousFunction.const ℕ (0 : A),
    BoundedContinuousFunction.const ℕ (1 : A), ?_⟩⟩
  intro h
  have h' := congrArg (fun f : ℕ →ᵇ A => f 0) h
  exact (zero_ne_one : (0 : A) ≠ 1) (by simpa using h')

local instance auxiliaryNontrivial : Nontrivial (AuxiliaryMatrixAlgebra A) := inferInstance

local instance auxiliaryOrder : PartialOrder (AuxiliaryMatrixAlgebra A) := CStarAlgebra.spectralOrder _
local instance auxiliaryStarOrder : StarOrderedRing (AuxiliaryMatrixAlgebra A) :=
  CStarAlgebra.spectralOrderedRing _

/-- The original algebra acts diagonally; the map is unital and multiplicative. -/
def diagonalConstants : A →⋆ₐ[ℂ] AuxiliaryMatrixAlgebra A where
  toFun a := diagonalHom (BoundedContinuousFunction.const ℕ a,
    BoundedContinuousFunction.const ℕ a)
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [CStarMatrix.one_apply]
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_star' a := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [CStarMatrix.star_apply]
  commutes' c := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [CStarMatrix.algebraMap_apply, Algebra.algebraMap_eq_smul_one]

def matrixUnit : AuxiliaryMatrixAlgebra A := corner (1 : ℕ →ᵇ A)

@[simp] theorem diagonalConstants_mul_matrixUnit (a : A) :
    diagonalConstants a * matrixUnit = corner (BoundedContinuousFunction.const ℕ a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagonalConstants, matrixUnit, CStarMatrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem norm_matrixUnit : ‖matrixUnit (A := A)‖ = 1 := by
  simp [matrixUnit]

def attainingUnitary (f : StrongDual ℂ A) : unitary (AuxiliaryMatrixAlgebra A) :=
  unitaryDilation (SequenceFunctional.attainer f) (SequenceFunctional.norm_attainer_le f)

def twisted (f : StrongDual ℂ A) : StrongDual ℂ (AuxiliaryMatrixAlgebra A) :=
  ((SequenceFunctional.extend f).comp entryMap).comp
    (ContinuousLinearMap.mul ℂ (AuxiliaryMatrixAlgebra A) (attainingUnitary f : AuxiliaryMatrixAlgebra A))

@[simp] theorem twisted_apply (f : StrongDual ℂ A) (M : AuxiliaryMatrixAlgebra A) :
    twisted f M = SequenceFunctional.extend f
      (entryMap ((attainingUnitary f : AuxiliaryMatrixAlgebra A) * M)) := rfl

theorem norm_twisted_le (f : StrongDual ℂ A) : ‖twisted f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro M
  calc
    ‖twisted f M‖ ≤ ‖SequenceFunctional.extend f‖ *
        ‖entryMap ((attainingUnitary f : AuxiliaryMatrixAlgebra A) * M)‖ :=
      (SequenceFunctional.extend f).le_opNorm _
    _ ≤ ‖f‖ * ‖(attainingUnitary f : AuxiliaryMatrixAlgebra A) * M‖ := by
      rw [SequenceFunctional.norm_extend]
      exact mul_le_mul_of_nonneg_left (entryMap_norm_le _) (norm_nonneg f)
    _ = ‖f‖ * ‖M‖ := by rw [CStarRing.norm_coe_unitary_mul]

@[simp] theorem twisted_one (f : StrongDual ℂ A) : twisted f 1 = (‖f‖ : ℂ) := by
  simp only [twisted_apply, mul_one, entryMap_apply, attainingUnitary,
    unitaryDilation_entry, SequenceFunctional.extend_attainer]

def auxiliaryState (f : StrongDual ℂ A) : StrongDual ℂ (AuxiliaryMatrixAlgebra A) :=
  (‖f‖ : ℂ)⁻¹ • twisted f

@[simp] theorem auxiliaryState_apply (f : StrongDual ℂ A) (M : AuxiliaryMatrixAlgebra A) :
    auxiliaryState f M = (‖f‖ : ℂ)⁻¹ * twisted f M := rfl

theorem auxiliaryState_norm_le (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ‖auxiliaryState f‖ ≤ 1 := by
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
  calc
    ‖auxiliaryState f‖ = ‖(‖f‖ : ℂ)⁻¹‖ * ‖twisted f‖ := norm_smul _ _
    _ ≤ ‖(‖f‖ : ℂ)⁻¹‖ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (norm_twisted_le f) (norm_nonneg _)
    _ = 1 := by simp [norm_inv, Complex.norm_real, abs_of_nonneg hnorm.le, hnorm.ne']

@[simp] theorem auxiliaryState_one (f : StrongDual ℂ A) (hf : f ≠ 0) :
    auxiliaryState f 1 = 1 := by
  have hn : (‖f‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hf)
  rw [auxiliaryState_apply, twisted_one, inv_mul_cancel₀ hn]

theorem auxiliaryState_mem (f : StrongDual ℂ A) (hf : f ≠ 0) :
    auxiliaryState f ∈ stateSpace (AuxiliaryMatrixAlgebra A) :=
  ⟨nonnegative_of_norm_le_one_of_apply_one _
    (auxiliaryState_norm_le f hf) (auxiliaryState_one f hf), auxiliaryState_one f hf⟩

/-- One fixed GNS model per nonzero functional. No Hilbert-space existence is assumed. -/
def positive (f : StrongDual ℂ A) (hf : f ≠ 0) : AuxiliaryMatrixAlgebra A →ₚ[ℂ] ℂ :=
  positiveLinearMapOfMemStateSpace _ (auxiliaryState_mem f hf)

abbrev GNSHilbertSpace (f : StrongDual ℂ A) (hf : f ≠ 0) := (positive f hf).GNS

def cyclicVector (f : StrongDual ℂ A) (hf : f ≠ 0) : GNSHilbertSpace f hf :=
  stateGNSVector _ (auxiliaryState_mem f hf)

theorem norm_cyclicVector (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ‖cyclicVector f hf‖ = 1 := norm_stateGNSVector _ (auxiliaryState_mem f hf)

def representation (f : StrongDual ℂ A) (hf : f ≠ 0) :
    A →⋆ₐ[ℂ] (GNSHilbertSpace f hf →L[ℂ] GNSHilbertSpace f hf) :=
  (positive f hf).gnsStarAlgHom.comp diagonalConstants

def leftVector (f : StrongDual ℂ A) (hf : f ≠ 0) : GNSHilbertSpace f hf :=
  (positive f hf).gnsStarAlgHom (attainingUnitary f : AuxiliaryMatrixAlgebra A) (cyclicVector f hf)

def rightVector (f : StrongDual ℂ A) (hf : f ≠ 0) : GNSHilbertSpace f hf :=
  (positive f hf).gnsStarAlgHom matrixUnit (cyclicVector f hf)

theorem norm_leftVector_le (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ‖leftVector f hf‖ ≤ 1 := by
  calc
    ‖leftVector f hf‖ ≤
        ‖(positive f hf).gnsStarAlgHom (attainingUnitary f : AuxiliaryMatrixAlgebra A)‖ *
          ‖cyclicVector f hf‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(attainingUnitary f : AuxiliaryMatrixAlgebra A)‖ * ‖cyclicVector f hf‖ :=
      mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le
          (positive f hf).gnsStarAlgHom.toNonUnitalStarAlgHom _) (norm_nonneg _)
    _ = 1 := by rw [CStarRing.norm_coe_unitary, norm_cyclicVector, one_mul]

theorem norm_rightVector_le (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ‖rightVector f hf‖ ≤ 1 := by
  calc
    ‖rightVector f hf‖ ≤ ‖(positive f hf).gnsStarAlgHom matrixUnit‖ *
        ‖cyclicVector f hf‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖matrixUnit (A := A)‖ * ‖cyclicVector f hf‖ :=
      mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le
          (positive f hf).gnsStarAlgHom.toNonUnitalStarAlgHom _) (norm_nonneg _)
    _ = 1 := by rw [norm_matrixUnit, norm_cyclicVector, one_mul]

/-- This identity fixes both the conjugation convention and the multiplication order. -/
theorem inner_coefficient (f : StrongDual ℂ A) (hf : f ≠ 0) (a : A) :
    inner ℂ (leftVector f hf) (representation f hf a (rightVector f hf)) =
      auxiliaryState f (star (attainingUnitary f : AuxiliaryMatrixAlgebra A) *
        corner (BoundedContinuousFunction.const ℕ a)) := by
  let P := (positive f hf).gnsStarAlgHom
  change inner ℂ (P _ (cyclicVector f hf))
    (P (diagonalConstants a) (P matrixUnit (cyclicVector f hf))) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (cyclicVector f hf)
    ((star (P (attainingUnitary f : AuxiliaryMatrixAlgebra A)) *
      (P (diagonalConstants a) * P matrixUnit)) (cyclicVector f hf)) = _
  rw [← map_star, ← map_mul, ← map_mul, diagonalConstants_mul_matrixUnit]
  exact inner_gnsStarAlgHom_stateGNSVector _ (auxiliaryState_mem f hf) _

/-- Exact recovery, with no factor-two loss and a single representation. -/
theorem recover (f : StrongDual ℂ A) (hf : f ≠ 0) (a : A) :
    f a = (‖f‖ : ℂ) *
      inner ℂ (leftVector f hf) (representation f hf a (rightVector f hf)) := by
  have hn : (‖f‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hf)
  rw [inner_coefficient, auxiliaryState_apply, ← mul_assoc, mul_inv_cancel₀ hn, one_mul,
    twisted_apply, ← mul_assoc, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul,
    entryMap_corner, SequenceFunctional.extend_const]

end MathlibAnnex.FunctionalCoefficient
