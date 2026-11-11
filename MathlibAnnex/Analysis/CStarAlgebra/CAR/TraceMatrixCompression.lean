/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The finite stages, trace representation and stage embeddings are existing
providers. The construction below uses their actual matrix entries. The
normalization of a nonzero range vector adapts the elementary argument in
Projection/MinimalColumn, without its internal-minimality hypothesis.
-/

import MathlibAnnex.Analysis.CStarAlgebra.CAR.TraceFiniteStages
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Matrix.Basis

/-!
# Positive unital compressions onto the represented CAR matrix stages

The domain is the full operator algebra on the existing trace Hilbert space.
For each actual matrix stage, choose a unit vector in the range of its `00`
matrix unit. Its translates by the `i0` matrix units give an isometric copy
of the defining finite-dimensional representation. Compress to that copy
and represent the resulting matrix back on the original trace Hilbert space.

Only the matrix algebra is finite-dimensional. Its represented matrix units
are not asserted to have finite rank or to be minimal in the trace von
Neumann algebra. No compatibility of the chosen vectors between stages is
needed, and no normality is claimed for the later cluster map.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.CStarAlgebra.CAR

local notation "Hτ" => TraceHilbertSpace
local notation "Bτ" => Hτ →L[ℂ] Hτ

/-- The actual matrix units of the represented `n`-th CAR stage. -/
def traceStageMatrixUnit (n : ℕ) (i j : Fin (2 ^ n)) : Bτ :=
  traceStageRepresentation n (CStarMatrix.ofMatrix (Matrix.single i j 1))

@[simp]
theorem star_traceStageMatrixUnit (n : ℕ) (i j : Fin (2 ^ n)) :
    star (traceStageMatrixUnit n i j) = traceStageMatrixUnit n j i := by
  rw [traceStageMatrixUnit, ← map_star]
  congr 1
  ext k l
  simp [CStarMatrix.star_apply, Matrix.single, and_comm]

/-- Matrix-unit multiplication takes place in the original operator algebra. -/
theorem traceStageMatrixUnit_mul (n : ℕ) (i j k l : Fin (2 ^ n)) :
    traceStageMatrixUnit n i j * traceStageMatrixUnit n k l =
      if j = k then traceStageMatrixUnit n i l else 0 := by
  classical
  by_cases h : j = k
  · subst k
    simp only [traceStageMatrixUnit, ← map_mul, if_true]
    congr 1
    exact (Matrix.single_mul_single_same (1 : ℂ) i j l 1).trans (by rw [one_mul]; rfl)
  · simp only [traceStageMatrixUnit, ← map_mul, if_neg h]
    have hzero : (CStarMatrix.ofMatrix (Matrix.single i j 1) : Stage n) *
        CStarMatrix.ofMatrix (Matrix.single k l 1) = 0 := by
      exact Matrix.single_mul_single_of_ne (1 : ℂ) i j k h 1
    rw [hzero, map_zero]

theorem traceStageMatrixUnit_diagonal_ne_zero (n : ℕ) (i : Fin (2 ^ n)) :
    traceStageMatrixUnit n i i ≠ 0 := by
  intro hzero
  have hinj : Function.Injective (traceStageRepresentation n) :=
    traceRepresentation_injective.comp (ofStage_injective n)
  have heq : (CStarMatrix.ofMatrix (Matrix.single i i 1) : Stage n) = 0 :=
    hinj (hzero.trans (map_zero (traceStageRepresentation n)).symm)
  have := congrArg (fun a : Stage n ↦ a i i) heq
  simpa using this

/-- A nonzero range vector of the `00` matrix unit can be normalized. No
minimal-projection assertion in the ambient von Neumann algebra is used. -/
theorem exists_unit_fixed_traceStageMatrixUnit (n : ℕ) :
    ∃ ξ : Hτ, traceStageMatrixUnit n 0 0 ξ = ξ ∧ ‖ξ‖ = 1 := by
  classical
  have hsome : ¬ ∀ η : Hτ, traceStageMatrixUnit n 0 0 η = 0 := by
    intro h
    exact traceStageMatrixUnit_diagonal_ne_zero n 0 (ContinuousLinearMap.ext h)
  obtain ⟨η, hη⟩ := not_forall.mp hsome
  let ζ : Hτ := traceStageMatrixUnit n 0 0 η
  have hζ : ζ ≠ 0 := hη
  have hfix : traceStageMatrixUnit n 0 0 ζ = ζ := by
    have hmul : traceStageMatrixUnit n 0 0 * traceStageMatrixUnit n 0 0 =
        traceStageMatrixUnit n 0 0 := by
      simpa using traceStageMatrixUnit_mul n 0 0 0 0
    exact congrArg (fun T : Bτ ↦ T η) hmul
  refine ⟨((‖ζ‖⁻¹ : ℝ) : ℂ) • ζ, ?_, ?_⟩
  · simp only [map_smul, hfix]
  · have hn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζ
    simp [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ζ)), hn]

/-- A fixed choice of a unit range vector, separately for each finite stage. -/
def traceStageUnitVector (n : ℕ) : Hτ :=
  Classical.choose (exists_unit_fixed_traceStageMatrixUnit n)

@[simp]
theorem traceStageMatrixUnit_apply_unitVector (n : ℕ) :
    traceStageMatrixUnit n 0 0 (traceStageUnitVector n) = traceStageUnitVector n :=
  (Classical.choose_spec (exists_unit_fixed_traceStageMatrixUnit n)).1

@[simp]
theorem norm_traceStageUnitVector (n : ℕ) : ‖traceStageUnitVector n‖ = 1 :=
  (Classical.choose_spec (exists_unit_fixed_traceStageMatrixUnit n)).2

/-- The column of translates of the chosen range vector. -/
def traceStageVector (n : ℕ) (i : Fin (2 ^ n)) : Hτ :=
  traceStageMatrixUnit n i 0 (traceStageUnitVector n)

/-- The finite column is orthonormal with the standard complex convention:
the first argument of the inner product is conjugate linear. -/
theorem inner_traceStageVector (n : ℕ) (i j : Fin (2 ^ n)) :
    inner ℂ (traceStageVector n i) (traceStageVector n j) =
      if i = j then 1 else 0 := by
  classical
  rw [traceStageVector, traceStageVector,
    ← (traceStageMatrixUnit n i 0).adjoint_inner_right]
  change inner ℂ (traceStageUnitVector n)
    ((star (traceStageMatrixUnit n i 0) * traceStageMatrixUnit n j 0)
      (traceStageUnitVector n)) = _
  rw [star_traceStageMatrixUnit, traceStageMatrixUnit_mul]
  by_cases hij : i = j
  · simp [hij, inner_self_eq_norm_sq_to_K]
  · simp [hij]

/-- The standard Euclidean operator associated to the existing matrix stage.
Both algebraic conversions are existing Mathlib equivalences. -/
def traceStageOperatorEquiv (n : ℕ) :
    Stage n ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (2 ^ n)) →L[ℂ] EuclideanSpace ℂ (Fin (2 ^ n))) :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans Matrix.toEuclideanCLM

@[simp]
theorem traceStageOperatorEquiv_apply (n : ℕ) (a : Stage n)
    (x : EuclideanSpace ℂ (Fin (2 ^ n))) (i : Fin (2 ^ n)) :
    traceStageOperatorEquiv n a x i = ∑ j, a i j * x j := rfl

/-- Synthesis of the orthonormal matrix-unit column, before bundling its norm. -/
def traceStageColumn (n : ℕ) : EuclideanSpace ℂ (Fin (2 ^ n)) →ₗ[ℂ] Hτ where
  toFun x := ∑ i, x i • traceStageVector n i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem inner_traceStageColumn (n : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 ^ n))) :
    inner ℂ (traceStageColumn n x) (traceStageColumn n y) = inner ℂ x y := by
  classical
  simp only [traceStageColumn, LinearMap.coe_mk, AddHom.coe_mk,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_traceStageVector]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_ite, ite_mul, mul_comm]

/-- An actual isometry from the defining finite Hilbert space into the same
CAR trace Hilbert space; it is not a surjective unitary on that space. -/
def traceStageIsometry (n : ℕ) :
    EuclideanSpace ℂ (Fin (2 ^ n)) →ₗᵢ[ℂ] Hτ :=
  (traceStageColumn n).isometryOfInner (inner_traceStageColumn n)

@[simp]
theorem traceStageIsometry_apply (n : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ n))) :
    traceStageIsometry n x = ∑ i, x i • traceStageVector n i := rfl

@[simp]
theorem traceStageIsometry_single (n : ℕ) (i : Fin (2 ^ n)) :
    traceStageIsometry n (EuclideanSpace.single i 1) = traceStageVector n i := by
  classical
  simp [traceStageIsometry_apply, PiLp.single_apply]

/-- A matrix acts on the column by its actual entries. -/
theorem traceStageRepresentation_apply_vector (n : ℕ) (a : Stage n)
    (j : Fin (2 ^ n)) :
    traceStageRepresentation n a (traceStageVector n j) =
      ∑ i, a i j • traceStageVector n i := by
  have hcol : a * CStarMatrix.ofMatrix (Matrix.single j (0 : Fin (2 ^ n)) 1) =
      ∑ i, a i j • CStarMatrix.ofMatrix (Matrix.single i (0 : Fin (2 ^ n)) 1) := by
    let b : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := CStarMatrix.ofMatrix.symm a
    have hm : b * Matrix.single j 0 1 = ∑ i, a i j • Matrix.single i 0 1 := by
      ext k l
      by_cases hl : l = 0
      · subst l
        rw [Matrix.mul_single_apply_same]
        simp [b, Matrix.single, Matrix.sum_apply, Matrix.smul_apply]
      · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]
        simp [Matrix.single, Matrix.sum_apply, Matrix.smul_apply, Ne.symm hl]
    have hm' := congrArg (CStarMatrix.ofMatrixₗ (R := ℂ)) hm
    rw [map_sum] at hm'
    simp only [map_smul] at hm'
    exact (Eq.trans (by rfl) hm').trans (by rfl)
  calc
    traceStageRepresentation n a (traceStageVector n j) =
        traceStageRepresentation n
          (a * CStarMatrix.ofMatrix (Matrix.single j 0 1)) (traceStageUnitVector n) := by
      simp only [map_mul, traceStageVector, traceStageMatrixUnit,
        ContinuousLinearMap.mul_apply]
    _ = ∑ i, a i j • traceStageVector n i := by
      rw [hcol]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, traceStageVector, traceStageMatrixUnit]

/-- The defining representation and the full trace-stage representation are
intertwined by the constructed isometry. -/
theorem traceStageRepresentation_comp_isometry (n : ℕ) (a : Stage n) :
    (traceStageRepresentation n a).comp (traceStageIsometry n).toContinuousLinearMap =
      (traceStageIsometry n).toContinuousLinearMap.comp (traceStageOperatorEquiv n a) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    traceStageIsometry_apply, map_sum, map_smul, traceStageRepresentation_apply_vector,
    traceStageOperatorEquiv_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Taking adjoints gives the second intertwining identity. -/
theorem traceStageIsometry_adjoint_comp (n : ℕ) (a : Stage n) :
    (traceStageIsometry n).toContinuousLinearMap.adjoint.comp
        (traceStageRepresentation n a) =
      (traceStageOperatorEquiv n a).comp
        (traceStageIsometry n).toContinuousLinearMap.adjoint := by
  have h := congrArg
    (fun S : EuclideanSpace ℂ (Fin (2 ^ n)) →L[ℂ] Hτ ↦ S.adjoint)
    (traceStageRepresentation_comp_isometry n (star a))
  simpa only [ContinuousLinearMap.adjoint_comp, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint] using h

/-- Compress to the actual defining matrix representation and represent the
result back on the original Hilbert space. This is a positive complex-linear
map on all bounded operators, not merely on the represented CAR algebra. -/
def traceMatrixCompression (n : ℕ) : Bτ →ₚ[ℂ] Bτ :=
  PositiveLinearMap.mk₀
    { toFun := fun T ↦ traceStageRepresentation n
        ((traceStageOperatorEquiv n).symm
          ((traceStageIsometry n).toContinuousLinearMap.adjoint.comp
            (T.comp (traceStageIsometry n).toContinuousLinearMap)))
      map_add' := by
        intro T S
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
        exact map_add ((traceStageRepresentation n).comp (traceStageOperatorEquiv n).symm.toStarAlgHom) _ _
      map_smul' := by
        intro c T
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
        exact map_smul ((traceStageRepresentation n).comp (traceStageOperatorEquiv n).symm.toStarAlgHom) c _ }
    (by
      intro T hT
      apply map_nonneg (traceStageRepresentation n)
      apply map_nonneg (traceStageOperatorEquiv n).symm.toStarAlgHom
      exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
        ((ContinuousLinearMap.nonneg_iff_isPositive.mp hT).adjoint_conj
          (traceStageIsometry n).toContinuousLinearMap))

theorem traceMatrixCompression_apply (n : ℕ) (T : Bτ) :
    traceMatrixCompression n T = traceStageRepresentation n
      ((traceStageOperatorEquiv n).symm
        ((traceStageIsometry n).toContinuousLinearMap.adjoint.comp
          (T.comp (traceStageIsometry n).toContinuousLinearMap))) := rfl

@[simp]
theorem traceMatrixCompression_one (n : ℕ) : traceMatrixCompression n 1 = 1 := by
  rw [traceMatrixCompression_apply]
  change traceStageRepresentation n ((traceStageOperatorEquiv n).symm
    ((traceStageIsometry n).toContinuousLinearMap.adjoint.comp
      ((ContinuousLinearMap.id ℂ Hτ).comp (traceStageIsometry n).toContinuousLinearMap))) = 1
  rw [ContinuousLinearMap.id_comp, LinearIsometry.adjoint_comp_self]
  exact map_one ((traceStageRepresentation n).comp (traceStageOperatorEquiv n).symm.toStarAlgHom)

/-- Every output belongs to the represented finite stage itself. -/
theorem traceMatrixCompression_mem_traceStageRange (n : ℕ) (T : Bτ) :
    traceMatrixCompression n T ∈ traceStageRange n :=
  ⟨(traceStageOperatorEquiv n).symm
    ((traceStageIsometry n).toContinuousLinearMap.adjoint.comp
      (T.comp (traceStageIsometry n).toContinuousLinearMap)), rfl⟩

/-- The compression fixes the actual represented matrix stage. -/
theorem traceMatrixCompression_traceStageRepresentation (n : ℕ) (a : Stage n) :
    traceMatrixCompression n (traceStageRepresentation n a) = traceStageRepresentation n a := by
  rw [traceMatrixCompression_apply, traceStageRepresentation_comp_isometry,
    ← ContinuousLinearMap.comp_assoc, LinearIsometry.adjoint_comp_self]
  change traceStageRepresentation n ((traceStageOperatorEquiv n).symm
    ((ContinuousLinearMap.id ℂ _).comp (traceStageOperatorEquiv n a))) = _
  rw [ContinuousLinearMap.id_comp, StarAlgEquiv.symm_apply_apply]

theorem traceMatrixCompression_of_mem (n : ℕ) (a : Bτ) (ha : a ∈ traceStageRange n) :
    traceMatrixCompression n a = a := by
  obtain ⟨x, rfl⟩ := ha
  exact traceMatrixCompression_traceStageRepresentation n x

/-- Multiplication on each side by elements of the represented finite stage
passes through the compression. The middle operator is arbitrary. -/
theorem traceMatrixCompression_mul_mul (n : ℕ) (a b T : Bτ)
    (ha : a ∈ traceStageRange n) (hb : b ∈ traceStageRange n) :
    traceMatrixCompression n (a * T * b) = a * traceMatrixCompression n T * b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [traceMatrixCompression_apply, traceMatrixCompression_apply]
  have hc : (traceStageIsometry n).toContinuousLinearMap.adjoint.comp
        ((traceStageRepresentation n x * T * traceStageRepresentation n y).comp
          (traceStageIsometry n).toContinuousLinearMap) =
      traceStageOperatorEquiv n x *
        ((traceStageIsometry n).toContinuousLinearMap.adjoint.comp
          (T.comp (traceStageIsometry n).toContinuousLinearMap)) *
        traceStageOperatorEquiv n y := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [traceStageRepresentation_comp_isometry]
    rw [← ContinuousLinearMap.comp_assoc
      (traceStageIsometry n).toContinuousLinearMap.adjoint
      (traceStageRepresentation n x), traceStageIsometry_adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  change traceStageRepresentation n ((traceStageOperatorEquiv n).symm _) =
    traceStageRepresentation n x * traceStageRepresentation n _ * traceStageRepresentation n y
  exact (congrArg (fun U ↦ traceStageRepresentation n ((traceStageOperatorEquiv n).symm U)) hc).trans (by
    let f := (traceStageRepresentation n).comp (traceStageOperatorEquiv n).symm.toStarAlgHom
    change f (_ * _ * _) = _
    rw [map_mul, map_mul]
    change traceStageRepresentation n ((traceStageOperatorEquiv n).symm (traceStageOperatorEquiv n x)) * _ * traceStageRepresentation n ((traceStageOperatorEquiv n).symm (traceStageOperatorEquiv n y)) = _
    rw [StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]
    rfl)

/-- These concrete finite-stage maps are contractions. In particular the
common pointwise compact family can use one uniform norm bound. -/
theorem norm_traceMatrixCompression_le (n : ℕ) (T : Bτ) :
    ‖traceMatrixCompression n T‖ ≤ ‖T‖ := by
  let V := (traceStageIsometry n).toContinuousLinearMap
  have hV : ‖V‖ ≤ 1 := V.opNorm_le_bound zero_le_one (by
    intro x
    rw [one_mul]
    exact ((traceStageIsometry n).norm_map x).le)
  have hV' : ‖V.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  rw [traceMatrixCompression_apply,
    NonUnitalStarAlgHom.norm_map (traceStageRepresentation n)
      (traceRepresentation_injective.comp (ofStage_injective n))]
  change ‖(traceStageOperatorEquiv n).symm.toStarAlgHom.toNonUnitalStarAlgHom (V.adjoint.comp (T.comp V))‖ ≤ ‖T‖
  rw [NonUnitalStarAlgHom.norm_map (traceStageOperatorEquiv n).symm.toStarAlgHom.toNonUnitalStarAlgHom
      (traceStageOperatorEquiv n).symm.injective]
  change ‖V.adjoint.comp (T.comp V)‖ ≤ ‖T‖
  calc
    ‖V.adjoint.comp (T.comp V)‖ ≤ ‖V.adjoint‖ * (‖T‖ * ‖V‖) :=
      (V.adjoint.opNorm_comp_le (T.comp V)).trans
        (mul_le_mul_of_nonneg_left (T.opNorm_comp_le V) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by simp

theorem continuous_traceMatrixCompression (n : ℕ) :
    Continuous (traceMatrixCompression n) := by
  exact map_continuous (traceMatrixCompression n)

end MathlibAnnex.CStarAlgebra.CAR
