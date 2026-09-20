import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The projective tensor norm for two normed spaces

This file specializes Mathlib's projective seminorm on a finite dependent
tensor product to two (possibly differently-universed) normed spaces over
`RCLike` scalars.  It proves both the pure-tensor norm formula and separation
of the seminorm.  The latter is not an assumption: a nonzero tensor is moved
to finite-dimensional subspaces, a nonzero basis coefficient is selected,
and its coordinate functionals are extended continuously by Hahn--Banach.
-/

set_option autoImplicit false

open scoped NNReal TensorProduct

namespace MathlibAnnex.ProjectiveTensorProduct

universe uK uE uF

noncomputable section

/-- A two-point index, presented as a sum so that Mathlib's sum-tensor
equivalence applies directly. -/
abbrev PairIndex : Type := PUnit ⊕ PUnit

/-- Universe-balanced family containing the two tensor factors. -/
abbrev PairFamily (E : Type uE) (F : Type uF) : PairIndex → Type (max uE uF) :=
  Sum.elim (fun _ ↦ ULift.{uF} E) (fun _ ↦ ULift.{uE} F)

variable (𝕜 : Type uK) [RCLike 𝕜]
variable (E : Type uE) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable abbrev pairNormed :
    ∀ i, NormedAddCommGroup (PairFamily E F i)
  | .inl _ => ULift.normedAddCommGroup
  | .inr _ => ULift.normedAddCommGroup

noncomputable abbrev instPairNormed (i : PairIndex) :
    NormedAddCommGroup (PairFamily E F i) := pairNormed E F i

attribute [instance] instPairNormed

private noncomputable abbrev pairModule : ∀ i, Module 𝕜 (PairFamily E F i)
  | .inl _ => ULift.module'
  | .inr _ => ULift.module'

private noncomputable abbrev instPairModule (i : PairIndex) :
    Module 𝕜 (PairFamily E F i) :=
  pairModule (𝕜 := 𝕜) (E := E) (F := F) i

attribute [local instance] instPairModule

noncomputable abbrev pairNormedSpace :
    ∀ i, NormedSpace 𝕜 (PairFamily E F i)
  | .inl _ => ULift.normedSpace
  | .inr _ => ULift.normedSpace

noncomputable abbrev instPairNormedSpace (i : PairIndex) :
    NormedSpace 𝕜 (PairFamily E F i) :=
  pairNormedSpace (𝕜 := 𝕜) (E := E) (F := F) i

attribute [instance] instPairNormedSpace
attribute [-instance] instPairModule

/-- The algebraic two-fold tensor product carrying Mathlib's projective
seminorm. -/
abbrev Algebraic := PiTensorProduct 𝕜 (PairFamily E F)

/-- The left factor in the universe-balanced presentation. -/
abbrev LeftFactor := PairFamily E F (.inl PUnit.unit)

/-- The right factor in the universe-balanced presentation. -/
abbrev RightFactor := PairFamily E F (.inr PUnit.unit)

/-- Algebraic identification with the ordinary binary tensor product. -/
def toTensor :
    Algebraic 𝕜 E F ≃ₗ[𝕜] (LeftFactor E F ⊗[𝕜] RightFactor E F) :=
  (PiTensorProduct.tmulEquivDep 𝕜 (PairFamily E F)).symm.trans <|
    TensorProduct.congr (PiTensorProduct.subsingletonEquiv PUnit.unit)
      (PiTensorProduct.subsingletonEquiv PUnit.unit)

/-- The dependent pair associated to `x` and `y`. -/
def pair (x : E) (y : F) : (i : PairIndex) → PairFamily E F i
  | .inl _ => ULift.up x
  | .inr _ => ULift.up y

/-- A pure tensor in the algebraic projective tensor product. -/
def pureAlgebraic (x : E) (y : F) : Algebraic 𝕜 E F :=
  PiTensorProduct.tprod 𝕜 (pair E F x y)

@[simp]
theorem toTensor_tprod (m : ∀ i, PairFamily E F i) :
    toTensor 𝕜 E F (PiTensorProduct.tprod 𝕜 m) =
      m (.inl PUnit.unit) ⊗ₜ[𝕜] m (.inr PUnit.unit) := by
  simp only [toTensor, LinearEquiv.trans_apply]
  rw [PiTensorProduct.tmulEquivDep_symm_apply]
  rw [TensorProduct.congr_tmul]
  rw [PiTensorProduct.subsingletonEquiv_apply_tprod,
    PiTensorProduct.subsingletonEquiv_apply_tprod]

private def pairMap
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜) :
    ∀ i, PairFamily E F i →L[𝕜] 𝕜
  | .inl _ => f
  | .inr _ => g

/-- Product of two continuous functionals, as a continuous bilinear map on
the balanced pair family. -/
def productMap
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜) :
    ContinuousMultilinearMap 𝕜 (PairFamily E F) 𝕜 :=
  (ContinuousMultilinearMap.mkPiAlgebra 𝕜 PairIndex 𝕜).compContinuousLinearMap
    (pairMap 𝕜 E F f g)

@[simp]
theorem productMap_apply
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜)
    (m : ∀ i, PairFamily E F i) :
    productMap 𝕜 E F f g m =
      f (m (.inl PUnit.unit)) * g (m (.inr PUnit.unit)) := by
  simp [productMap, pairMap, ContinuousMultilinearMap.mkPiAlgebra_apply,
    Fintype.prod_sum_type]

theorem norm_productMap_le
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜) :
    ‖productMap 𝕜 E F f g‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    ‖productMap 𝕜 E F f g‖ ≤
        ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 PairIndex 𝕜‖ *
          ∏ i, ‖pairMap 𝕜 E F f g i‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1 * (‖f‖ * ‖g‖) := by
      rw [show ∏ i, ‖pairMap 𝕜 E F f g i‖ = ‖f‖ * ‖g‖ by
        simp [Fintype.prod_sum_type, pairMap]]
      exact mul_le_mul_of_nonneg_right
        (ContinuousMultilinearMap.norm_mkPiAlgebra_le
          (𝕜 := 𝕜) (ι := PairIndex) (A := 𝕜)) (by positivity)
    _ = ‖f‖ * ‖g‖ := one_mul _

@[simp]
theorem norm_pair_left (x : E) (y : F) :
    ‖pair E F x y (.inl PUnit.unit)‖ = ‖x‖ := rfl

@[simp]
theorem norm_pair_right (x : E) (y : F) :
    ‖pair E F x y (.inr PUnit.unit)‖ = ‖y‖ := rfl

/-- The projective seminorm has the expected value on a pure tensor. -/
@[simp]
theorem norm_pureAlgebraic (x : E) (y : F) :
    ‖pureAlgebraic 𝕜 E F x y‖ = ‖x‖ * ‖y‖ := by
  apply le_antisymm
  · change PiTensorProduct.projectiveSeminorm (pureAlgebraic 𝕜 E F x y) ≤
      ‖x‖ * ‖y‖
    calc
      PiTensorProduct.projectiveSeminorm (pureAlgebraic 𝕜 E F x y) ≤
          ∏ i, ‖pair E F x y i‖ := by
        exact PiTensorProduct.projectiveSeminorm_tprod_le (pair E F x y)
      _ = ‖x‖ * ‖y‖ := by simp [Fintype.prod_sum_type, pair]
  · obtain ⟨f, hf, hfx⟩ :=
      exists_dual_vector'' 𝕜 (pair E F x y (.inl PUnit.unit))
    obtain ⟨g, hg, hgy⟩ :=
      exists_dual_vector'' 𝕜 (pair E F x y (.inr PUnit.unit))
    have hB : ‖productMap 𝕜 E F f g‖ ≤ 1 := by
      refine (norm_productMap_le 𝕜 E F f g).trans ?_
      nlinarith [norm_nonneg f, norm_nonneg g]
    calc
      ‖x‖ * ‖y‖ =
          ‖(PiTensorProduct.lift (productMap 𝕜 E F f g).toMultilinearMap)
            (pureAlgebraic 𝕜 E F x y)‖ := by
              simp only [pureAlgebraic, PiTensorProduct.lift.tprod]
              change ‖x‖ * ‖y‖ =
                ‖productMap 𝕜 E F f g (pair E F x y)‖
              rw [productMap_apply, hfx, hgy]
              rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal]
              simp only [abs_of_nonneg (norm_nonneg _)]
              rfl
      _ ≤ ‖productMap 𝕜 E F f g‖ * ‖pureAlgebraic 𝕜 E F x y‖ :=
        PiTensorProduct.norm_eval_le_projectiveSeminorm
          (productMap 𝕜 E F f g) (pureAlgebraic 𝕜 E F x y)
      _ ≤ 1 * ‖pureAlgebraic 𝕜 E F x y‖ :=
        mul_le_mul_of_nonneg_right hB (norm_nonneg _)
      _ = ‖pureAlgebraic 𝕜 E F x y‖ := one_mul _

private def tensorEval
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜) :
    LeftFactor E F ⊗[𝕜] RightFactor E F →ₗ[𝕜] 𝕜 :=
  TensorProduct.lift <|
    (LinearMap.mul 𝕜 𝕜).compl₁₂ f.toLinearMap g.toLinearMap

@[simp]
private theorem tensorEval_tmul
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜)
    (x : LeftFactor E F) (y : RightFactor E F) :
    tensorEval 𝕜 E F f g (x ⊗ₜ[𝕜] y) = f x * g y := rfl

private theorem lift_productMap_eq_tensorEval
    (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜)
    (z : Algebraic 𝕜 E F) :
    (PiTensorProduct.lift (productMap 𝕜 E F f g).toMultilinearMap) z =
      tensorEval 𝕜 E F f g (toTensor 𝕜 E F z) := by
  let q : Algebraic 𝕜 E F →ₗ[𝕜] 𝕜 :=
    tensorEval 𝕜 E F f g ∘ₗ (toTensor 𝕜 E F).toLinearMap
  have hq : q = PiTensorProduct.lift (productMap 𝕜 E F f g).toMultilinearMap := by
    apply PiTensorProduct.lift.unique
    intro m
    change tensorEval 𝕜 E F f g
        (toTensor 𝕜 E F (PiTensorProduct.tprod 𝕜 m)) =
      productMap 𝕜 E F f g m
    rw [toTensor_tprod, tensorEval_tmul, productMap_apply]
  exact LinearMap.congr_fun hq.symm z

private theorem exists_lift_productMap_ne_zero
    (z : Algebraic 𝕜 E F) (hz : z ≠ 0) :
    ∃ (f : LeftFactor E F →L[𝕜] 𝕜) (g : RightFactor E F →L[𝕜] 𝕜),
      (PiTensorProduct.lift (productMap 𝕜 E F f g).toMultilinearMap) z ≠ 0 := by
  let t := toTensor 𝕜 E F z
  have ht : t ≠ 0 := (toTensor 𝕜 E F).map_ne_zero_iff.mpr hz
  obtain ⟨M, N, hM, hN, hsub⟩ :=
    TensorProduct.exists_finite_submodule_of_setFinite {t} (Set.finite_singleton t)
  obtain ⟨w, hw⟩ := Set.singleton_subset_iff.mp hsub
  have hw0 : w ≠ 0 := by
    intro hw0
    apply ht
    rw [← hw, hw0]
    exact LinearMap.map_zero _
  letI : Module.Finite 𝕜 M := hM
  letI : Module.Finite 𝕜 N := hN
  let bM := Module.finBasis 𝕜 M
  let bN := Module.finBasis 𝕜 N
  have hrepr : (bM.tensorProduct bN).repr w ≠ 0 :=
    (bM.tensorProduct bN).repr.map_ne_zero_iff.mpr hw0
  obtain ⟨ij, hij⟩ := not_forall.mp fun h ↦ hrepr (Finsupp.ext h)
  have hsM : Function.Surjective
      (M.subtype.dualMap ∘ ContinuousLinearMap.toLinearMap) :=
    (SeparatingDual.dualMap_surjective_iff (R := 𝕜)
      (V := LeftFactor E F)).2 M.subtype_injective
  have hsN : Function.Surjective
      (N.subtype.dualMap ∘ ContinuousLinearMap.toLinearMap) :=
    (SeparatingDual.dualMap_surjective_iff (R := 𝕜)
      (V := RightFactor E F)).2 N.subtype_injective
  obtain ⟨f, hf⟩ := hsM (bM.coord ij.1)
  obtain ⟨g, hg⟩ := hsN (bN.coord ij.2)
  refine ⟨f, g, ?_⟩
  rw [lift_productMap_eq_tensorEval]
  change tensorEval 𝕜 E F f g t ≠ 0
  rw [← hw]
  have hf_apply (m : M) : f m.1 = bM.coord ij.1 m := by
    have h := LinearMap.congr_fun hf m
    simp only [Function.comp_apply, LinearMap.dualMap_apply] at h
    change f m.1 = bM.coord ij.1 m at h
    exact h
  have hg_apply (n : N) : g n.1 = bN.coord ij.2 n := by
    have h := LinearMap.congr_fun hg n
    simp only [Function.comp_apply, LinearMap.dualMap_apply] at h
    change g n.1 = bN.coord ij.2 n at h
    exact h
  have hlin :
      tensorEval 𝕜 E F f g ∘ₗ TensorProduct.mapIncl M N =
        (bM.tensorProduct bN).coord ij := by
    apply TensorProduct.ext'
    intro m n
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorEval_tmul]
    change f m.1 * g n.1 = (bM.tensorProduct bN).repr (m ⊗ₜ[𝕜] n) ij
    rw [hf_apply, hg_apply, Module.Basis.tensorProduct_repr_tmul_apply]
    simp only [Module.Basis.coord_apply, smul_eq_mul, mul_comm]
  have heval := LinearMap.congr_fun hlin w
  change tensorEval 𝕜 E F f g (TensorProduct.mapIncl M N w) =
    (bM.tensorProduct bN).repr w ij at heval
  rw [heval]
  exact hij

/-- Over `ℝ` or `ℂ`, Mathlib's projective seminorm on the binary algebraic
tensor product is separated. -/
theorem eq_zero_of_norm_eq_zero (z : Algebraic 𝕜 E F) (hz : ‖z‖ = 0) : z = 0 := by
  by_contra hne
  obtain ⟨f, g, hfg⟩ := exists_lift_productMap_ne_zero 𝕜 E F z hne
  have hbound := PiTensorProduct.norm_eval_le_projectiveSeminorm
    (productMap 𝕜 E F f g) z
  rw [hz, mul_zero] at hbound
  have hnorm :
      ‖(PiTensorProduct.lift (productMap 𝕜 E F f g).toMultilinearMap) z‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  exact hfg (norm_eq_zero.mp hnorm)

/-- The separated projective normed-group structure.  This reuses the
projective seminorm already installed by Mathlib; it does not install a second
global norm. -/
instance instNormedAddCommGroupAlgebraic :
    NormedAddCommGroup (Algebraic 𝕜 E F) :=
  NormedAddCommGroup.ofSeparation (eq_zero_of_norm_eq_zero 𝕜 E F)

/-- The completed projective tensor product. -/
abbrev Completion := UniformSpace.Completion (Algebraic 𝕜 E F)

/-- Canonical map from the algebraic tensor product into its completion. -/
def toCompletion : Algebraic 𝕜 E F →L[𝕜] Completion 𝕜 E F :=
  UniformSpace.Completion.toComplL

/-- The algebraic projective tensor embeds injectively in its completion. -/
theorem toCompletion_injective : Function.Injective (toCompletion 𝕜 E F) :=
  by
    simpa [toCompletion] using
      (UniformSpace.Completion.coe_injective (Algebraic 𝕜 E F) :
        Function.Injective ((↑) : Algebraic 𝕜 E F → Completion 𝕜 E F))

/-- The algebraic projective tensors have dense image in the completion. -/
theorem denseRange_toCompletion : DenseRange (toCompletion 𝕜 E F) := by
  simpa [toCompletion] using
    (UniformSpace.Completion.denseRange_coe :
      DenseRange ((↑) : Algebraic 𝕜 E F → Completion 𝕜 E F))

/-- A pure tensor in the completed projective tensor product. -/
def tprod (x : E) (y : F) : Completion 𝕜 E F :=
  toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y)

@[simp]
theorem tprod_zero_left (y : F) : tprod 𝕜 E F 0 y = 0 := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F 0 y) = 0
  rw [← map_zero (toCompletion 𝕜 E F)]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_zero]
  unfold pureAlgebraic
  rw [toTensor_tprod]
  change ULift.up (0 : E) ⊗ₜ[𝕜] ULift.up y = 0
  rw [show ULift.up (0 : E) = 0 by rfl, TensorProduct.zero_tmul]

@[simp]
theorem tprod_zero_right (x : E) : tprod 𝕜 E F x 0 = 0 := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x 0) = 0
  rw [← map_zero (toCompletion 𝕜 E F)]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_zero]
  unfold pureAlgebraic
  rw [toTensor_tprod]
  change ULift.up x ⊗ₜ[𝕜] ULift.up (0 : F) = 0
  rw [show ULift.up (0 : F) = 0 by rfl, TensorProduct.tmul_zero]

theorem tprod_add_left (x x' : E) (y : F) :
    tprod 𝕜 E F (x + x') y = tprod 𝕜 E F x y + tprod 𝕜 E F x' y := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F (x + x') y) = _
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F (x + x') y) =
    toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y) +
      toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x' y)
  rw [← map_add]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_add]
  unfold pureAlgebraic
  rw [toTensor_tprod, toTensor_tprod, toTensor_tprod]
  change ULift.up (x + x') ⊗ₜ[𝕜] ULift.up y =
    ULift.up x ⊗ₜ[𝕜] ULift.up y + ULift.up x' ⊗ₜ[𝕜] ULift.up y
  rw [show ULift.up (x + x') = ULift.up x + ULift.up x' by rfl,
    TensorProduct.add_tmul]

theorem tprod_add_right (x : E) (y y' : F) :
    tprod 𝕜 E F x (y + y') = tprod 𝕜 E F x y + tprod 𝕜 E F x y' := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x (y + y')) = _
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x (y + y')) =
    toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y) +
      toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y')
  rw [← map_add]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_add]
  unfold pureAlgebraic
  rw [toTensor_tprod, toTensor_tprod, toTensor_tprod]
  change ULift.up x ⊗ₜ[𝕜] ULift.up (y + y') =
    ULift.up x ⊗ₜ[𝕜] ULift.up y + ULift.up x ⊗ₜ[𝕜] ULift.up y'
  rw [show ULift.up (y + y') = ULift.up y + ULift.up y' by rfl,
    TensorProduct.tmul_add]

theorem tprod_smul_left (c : 𝕜) (x : E) (y : F) :
    tprod 𝕜 E F (c • x) y = c • tprod 𝕜 E F x y := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F (c • x) y) = _
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F (c • x) y) =
    c • toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y)
  rw [← map_smul]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_smul]
  unfold pureAlgebraic
  rw [toTensor_tprod, toTensor_tprod]
  change ULift.up (c • x) ⊗ₜ[𝕜] ULift.up y =
    c • (ULift.up x ⊗ₜ[𝕜] ULift.up y)
  rw [show ULift.up (c • x) = c • ULift.up x by rfl]
  exact (TensorProduct.smul_tmul' c _ _).symm

theorem tprod_smul_right (c : 𝕜) (x : E) (y : F) :
    tprod 𝕜 E F x (c • y) = c • tprod 𝕜 E F x y := by
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x (c • y)) = _
  change toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x (c • y)) =
    c • toCompletion 𝕜 E F (pureAlgebraic 𝕜 E F x y)
  rw [← map_smul]
  congr 1
  apply (toTensor 𝕜 E F).injective
  rw [map_smul]
  unfold pureAlgebraic
  rw [toTensor_tprod, toTensor_tprod]
  change ULift.up x ⊗ₜ[𝕜] ULift.up (c • y) =
    c • (ULift.up x ⊗ₜ[𝕜] ULift.up y)
  rw [show ULift.up (c • y) = c • ULift.up y by rfl]
  calc
    ULift.up x ⊗ₜ[𝕜] (c • ULift.up y) =
        (c • ULift.up x) ⊗ₜ[𝕜] ULift.up y :=
      TensorProduct.tmul_smul c _ _
    _ = c • (ULift.up x ⊗ₜ[𝕜] ULift.up y) :=
      (TensorProduct.smul_tmul' c _ _).symm

@[simp]
theorem tprod_neg_left (x : E) (y : F) :
    tprod 𝕜 E F (-x) y = -tprod 𝕜 E F x y := by
  simpa only [neg_one_smul] using tprod_smul_left 𝕜 E F (-1) x y

@[simp]
theorem tprod_neg_right (x : E) (y : F) :
    tprod 𝕜 E F x (-y) = -tprod 𝕜 E F x y := by
  simpa only [neg_one_smul] using tprod_smul_right 𝕜 E F (-1) x y

/-- Pure tensors retain their product norm after completion. -/
@[simp]
theorem norm_tprod (x : E) (y : F) :
    ‖tprod 𝕜 E F x y‖ = ‖x‖ * ‖y‖ := by
  change ‖(↑(pureAlgebraic 𝕜 E F x y) : Completion 𝕜 E F)‖ =
    ‖x‖ * ‖y‖
  rw [UniformSpace.Completion.norm_coe]
  exact norm_pureAlgebraic 𝕜 E F x y

/-- The standard projective upper bound for a finite presentation. -/
theorem norm_sum_tprod_le {ι : Type*} [Fintype ι]
    (x : ι → E) (y : ι → F) :
    ‖∑ i, tprod 𝕜 E F (x i) (y i)‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
  calc
    ‖∑ i, tprod 𝕜 E F (x i) (y i)‖ ≤
        ∑ i, ‖tprod 𝕜 E F (x i) (y i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖y i‖ := by simp

section Universal

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Bounded bilinear maps on the two ordinary factors, represented on the
universe-balanced two-point family.  Evaluation on `E × F` is provided by
`BoundedBilinearMap.apply`. -/
abbrev BoundedBilinearMap := ContinuousMultilinearMap 𝕜 (PairFamily E F) G

namespace BoundedBilinearMap

/-- Evaluate a bounded bilinear map on the original, unlifted factors. -/
def apply (B : BoundedBilinearMap 𝕜 E F G) (x : E) (y : F) : G :=
  B (pair E F x y)

private def ofContinuousLinearMapLinear (B : E →L[𝕜] F →L[𝕜] G) :
    MultilinearMap 𝕜 (PairFamily E F) G where
  toFun m := B (m (.inl PUnit.unit)).down (m (.inr PUnit.unit)).down
  map_update_add' m i x y := by
    rcases i with i | i <;> cases i
    · simp [Function.update]
      change B (x.down + y.down) (m (.inr PUnit.unit)).down = _
      simp
    · simp [Function.update]
      change B (m (.inl PUnit.unit)).down (x.down + y.down) = _
      simp
  map_update_smul' m i c x := by
    rcases i with i | i <;> cases i
    · simp [Function.update]
      change B (c • x.down) (m (.inr PUnit.unit)).down = _
      simp
    · simp [Function.update]
      change B (m (.inl PUnit.unit)).down (c • x.down) = _
      simp

/-- Regard the usual curried continuous bilinear map as a bounded bilinear map
on the balanced pair family. -/
def ofContinuousLinearMap (B : E →L[𝕜] F →L[𝕜] G) :
    BoundedBilinearMap 𝕜 E F G :=
  (ofContinuousLinearMapLinear 𝕜 E F G B).mkContinuous ‖B‖ fun m ↦ by
    calc
      ‖B (m (.inl PUnit.unit)).down (m (.inr PUnit.unit)).down‖ ≤
          ‖B (m (.inl PUnit.unit)).down‖ * ‖(m (.inr PUnit.unit)).down‖ :=
        (B (m (.inl PUnit.unit)).down).le_opNorm _
      _ ≤ (‖B‖ * ‖(m (.inl PUnit.unit)).down‖) *
          ‖(m (.inr PUnit.unit)).down‖ := by
        gcongr
        exact B.le_opNorm _
      _ = ‖B‖ * ∏ i, ‖m i‖ := by
        simp [Fintype.prod_sum_type, mul_assoc]

@[simp]
theorem ofContinuousLinearMap_apply (B : E →L[𝕜] F →L[𝕜] G)
    (x : E) (y : F) :
    apply 𝕜 E F G (ofContinuousLinearMap 𝕜 E F G B) x y = B x y := rfl

/-- The ordinary curried operator norm agrees with the multilinear operator
norm used by the projective universal property. -/
@[simp]
theorem norm_ofContinuousLinearMap (B : E →L[𝕜] F →L[𝕜] G) :
    ‖ofContinuousLinearMap 𝕜 E F G B‖ = ‖B‖ := by
  apply le_antisymm
  · exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg B) _
  · refine ContinuousLinearMap.opNorm_le_bound B (norm_nonneg _) fun x ↦ ?_
    refine ContinuousLinearMap.opNorm_le_bound (B x) (by positivity) fun y ↦ ?_
    have h := (ofContinuousLinearMap 𝕜 E F G B).le_opNorm (pair E F x y)
    change ‖B x y‖ ≤ ‖ofContinuousLinearMap 𝕜 E F G B‖ *
      ∏ i, ‖pair E F x y i‖ at h
    simpa [Fintype.prod_sum_type, pair, mul_assoc] using h

end BoundedBilinearMap

/-- Mathlib's isometric universal correspondence on the algebraic projective
tensor product. -/
def algebraicLiftIsometry :
    BoundedBilinearMap 𝕜 E F G ≃ₗᵢ[𝕜]
      (Algebraic 𝕜 E F →L[𝕜] G) :=
  PiTensorProduct.liftIsometry 𝕜 (PairFamily E F) G

variable [CompleteSpace G]

private theorem isUniformInducing_toCompletion :
    IsUniformInducing (toCompletion 𝕜 E F) := by
  simpa [toCompletion] using
    (UniformSpace.Completion.isUniformInducing_coe (Algebraic 𝕜 E F))

/-- Extend a continuous linear map uniquely from the algebraic projective
tensor product to its completion. -/
def completionExtend (f : Algebraic 𝕜 E F →L[𝕜] G) :
    Completion 𝕜 E F →L[𝕜] G :=
  f.extend (toCompletion 𝕜 E F)

@[simp]
theorem completionExtend_toCompletion
    (f : Algebraic 𝕜 E F →L[𝕜] G) (z : Algebraic 𝕜 E F) :
    completionExtend 𝕜 E F G f (toCompletion 𝕜 E F z) = f z :=
  ContinuousLinearMap.extend_eq f (denseRange_toCompletion 𝕜 E F)
    (isUniformInducing_toCompletion 𝕜 E F) z

/-- Two continuous linear maps out of the completed projective tensor product
are equal when they agree on ordinary pure tensors. -/
theorem ext_tprod {f g : Completion 𝕜 E F →L[𝕜] G}
    (h : ∀ x y, f (tprod 𝕜 E F x y) = g (tprod 𝕜 E F x y)) :
    f = g := by
  have hdense : (fun z ↦ f (toCompletion 𝕜 E F z)) =
      fun z ↦ g (toCompletion 𝕜 E F z) := by
    funext z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r p =>
        simp only [map_smul]
        apply congrArg (r • ·)
        let x : E := (p (.inl PUnit.unit)).down
        let y : F := (p (.inr PUnit.unit)).down
        have hp : p = pair E F x y := by
          funext i
          rcases i with i | i <;> cases i <;> rfl
        rw [hp]
        exact h x y
    | add z w hz hw => simp only [map_add, hz, hw]
  have heq : (fun z ↦ f z) = fun z ↦ g z :=
    (denseRange_toCompletion 𝕜 E F).equalizer f.continuous g.continuous hdense
  apply ContinuousLinearMap.ext
  exact congrFun heq

/-- Extension to the completion is linear in the map being extended. -/
def completionExtendL :
    (Algebraic 𝕜 E F →L[𝕜] G) →ₗ[𝕜]
      (Completion 𝕜 E F →L[𝕜] G) where
  toFun := completionExtend 𝕜 E F G
  map_add' f g := by
    apply ContinuousLinearMap.extend_unique (f + g)
      (denseRange_toCompletion 𝕜 E F)
      (isUniformInducing_toCompletion 𝕜 E F)
    apply ContinuousLinearMap.ext
    intro z
    simp
  map_smul' c f := by
    apply ContinuousLinearMap.extend_unique (c • f)
      (denseRange_toCompletion 𝕜 E F)
      (isUniformInducing_toCompletion 𝕜 E F)
    apply ContinuousLinearMap.ext
    intro z
    simp

/-- Restriction along the dense isometric inclusion. -/
def completionRestrictL :
    (Completion 𝕜 E F →L[𝕜] G) →ₗ[𝕜]
      (Algebraic 𝕜 E F →L[𝕜] G) where
  toFun f := f.comp (toCompletion 𝕜 E F)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Continuous linear maps from the completion are exactly the continuous
linear maps on the dense algebraic tensor product. -/
def completionLinearEquiv :
    (Algebraic 𝕜 E F →L[𝕜] G) ≃ₗ[𝕜]
      (Completion 𝕜 E F →L[𝕜] G) where
  toLinearMap := completionExtendL 𝕜 E F G
  invFun := completionRestrictL 𝕜 E F G
  left_inv f := by
    apply ContinuousLinearMap.ext
    intro z
    simp [completionRestrictL, completionExtendL]
  right_inv f := by
    apply ContinuousLinearMap.extend_unique
      (f.comp (toCompletion 𝕜 E F))
      (denseRange_toCompletion 𝕜 E F)
      (isUniformInducing_toCompletion 𝕜 E F)
    rfl

/-- Completion extension preserves the operator norm. -/
theorem norm_completionExtend
    (f : Algebraic 𝕜 E F →L[𝕜] G) :
    ‖completionExtend 𝕜 E F G f‖ = ‖f‖ := by
  apply le_antisymm
  · have h := ContinuousLinearMap.opNorm_extend_le f
      (denseRange_toCompletion 𝕜 E F) (N := (1 : ℝ≥0)) (fun z ↦ by
        simp [toCompletion])
    simpa [completionExtend] using h
  · refine ContinuousLinearMap.opNorm_le_bound f
      (norm_nonneg (completionExtend 𝕜 E F G f)) fun z ↦ ?_
    have h := (completionExtend 𝕜 E F G f).le_opNorm
      (toCompletion 𝕜 E F z)
    rw [completionExtend_toCompletion] at h
    simpa [toCompletion] using h

/-- Isometric equivalence between maps on the algebraic tensor and maps on
its completion. -/
def completionLiftIsometry :
    (Algebraic 𝕜 E F →L[𝕜] G) ≃ₗᵢ[𝕜]
      (Completion 𝕜 E F →L[𝕜] G) where
  __ := completionLinearEquiv 𝕜 E F G
  norm_map' := norm_completionExtend 𝕜 E F G

/-- The isometric universal correspondence between bounded bilinear maps and
continuous linear maps on the completed projective tensor product. -/
def liftIsometry :
    BoundedBilinearMap 𝕜 E F G ≃ₗᵢ[𝕜]
      (Completion 𝕜 E F →L[𝕜] G) :=
  (algebraicLiftIsometry 𝕜 E F G).trans
    (completionLiftIsometry 𝕜 E F G)

@[simp]
theorem liftIsometry_tprod (B : BoundedBilinearMap 𝕜 E F G) (x : E) (y : F) :
    liftIsometry 𝕜 E F G B (tprod 𝕜 E F x y) =
      BoundedBilinearMap.apply 𝕜 E F G B x y := by
  simp [liftIsometry, algebraicLiftIsometry, completionLiftIsometry,
    completionLinearEquiv, completionExtendL, tprod,
    BoundedBilinearMap.apply, pureAlgebraic]

/-- The dual of the completed projective tensor product is isometrically the
space of bounded bilinear forms. -/
def dualIsometry :
    StrongDual 𝕜 (Completion 𝕜 E F) ≃ₗᵢ[𝕜]
      BoundedBilinearMap 𝕜 E F 𝕜 :=
  (liftIsometry 𝕜 E F 𝕜).symm

@[simp]
theorem dualIsometry_apply (f : StrongDual 𝕜 (Completion 𝕜 E F))
    (x : E) (y : F) :
    BoundedBilinearMap.apply 𝕜 E F 𝕜 (dualIsometry 𝕜 E F f) x y =
      f (tprod 𝕜 E F x y) := by
  have h := liftIsometry_tprod 𝕜 E F 𝕜
    (dualIsometry 𝕜 E F f) x y
  simpa [dualIsometry] using h.symm

end Universal

section Functorial

universe uE' uF' uL uR

variable (E' : Type uE') [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (F' : Type uF') [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Lift a continuous linear map through arbitrary universe lifts. -/
def uliftMap {V : Type uE} {W : Type uE'}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (f : V →L[𝕜] W) : ULift.{uL} V →L[𝕜] ULift.{uR} W :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ULift.up (f x.down)
      map_add' := by
        intro x y
        apply ULift.ext
        simp
      map_smul' := by
        intro c x
        apply ULift.ext
        simp }
    ‖f‖ fun x ↦ by simpa using f.le_opNorm x.down

@[simp]
theorem uliftMap_apply {V : Type uE} {W : Type uE'}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (f : V →L[𝕜] W) (x : ULift.{uL} V) :
    uliftMap (𝕜 := 𝕜) f x = ULift.up (f x.down) := rfl

theorem norm_uliftMap_le {V : Type uE} {W : Type uE'}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (f : V →L[𝕜] W) :
    ‖(uliftMap (𝕜 := 𝕜) f : ULift.{uL} V →L[𝕜] ULift.{uR} W)‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

private def pairFamilyMap (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ∀ i, PairFamily E F i →L[𝕜] PairFamily E' F' i
  | .inl _ => uliftMap (𝕜 := 𝕜) f
  | .inr _ => uliftMap (𝕜 := 𝕜) g

/-- Functorial map on algebraic projective tensors, using Mathlib's `mapL`. -/
def mapAlgebraic (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    Algebraic 𝕜 E F →L[𝕜] Algebraic 𝕜 E' F' :=
  PiTensorProduct.mapL (pairFamilyMap 𝕜 E F E' F' f g)

/-- Functorial map on completed projective tensors. -/
def map (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    Completion 𝕜 E F →L[𝕜] Completion 𝕜 E' F' :=
  completionExtend 𝕜 E F (Completion 𝕜 E' F') <|
    (toCompletion 𝕜 E' F').comp (mapAlgebraic 𝕜 E F E' F' f g)

@[simp]
theorem map_tprod (f : E →L[𝕜] E') (g : F →L[𝕜] F') (x : E) (y : F) :
    map 𝕜 E F E' F' f g (tprod 𝕜 E F x y) =
      tprod 𝕜 E' F' (f x) (g y) := by
  rw [map, tprod, completionExtend_toCompletion]
  change toCompletion 𝕜 E' F'
      (PiTensorProduct.map (fun i ↦ (pairFamilyMap 𝕜 E F E' F' f g i).toLinearMap)
        (pureAlgebraic 𝕜 E F x y)) = _
  rw [pureAlgebraic, PiTensorProduct.map_tprod, tprod]
  congr 2
  funext i
  rcases i with i | i <;> cases i <;> rfl

theorem norm_map_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ‖map 𝕜 E F E' F' f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [map, norm_completionExtend]
  have hto : ‖toCompletion 𝕜 E' F'‖ ≤ 1 := by
    simpa [toCompletion, UniformSpace.Completion.toComplL] using
      (UniformSpace.Completion.toComplₗᵢ
        (𝕜 := 𝕜) (E := Algebraic 𝕜 E' F')).norm_toContinuousLinearMap_le
  have hmap : ‖mapAlgebraic 𝕜 E F E' F' f g‖ ≤
      ∏ i, ‖pairFamilyMap 𝕜 E F E' F' f g i‖ :=
    PiTensorProduct.opNorm_mapL _
  have hprod : (∏ i, ‖pairFamilyMap 𝕜 E F E' F' f g i‖) ≤ ‖f‖ * ‖g‖ := by
    rw [Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, pairFamilyMap]
    exact mul_le_mul
      (norm_uliftMap_le (𝕜 := 𝕜) f)
      (norm_uliftMap_le (𝕜 := 𝕜) g)
      (norm_nonneg _) (norm_nonneg _)
  calc
    ‖(toCompletion 𝕜 E' F').comp (mapAlgebraic 𝕜 E F E' F' f g)‖ ≤
        ‖toCompletion 𝕜 E' F'‖ * ‖mapAlgebraic 𝕜 E F E' F' f g‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (∏ i, ‖pairFamilyMap 𝕜 E F E' F' f g i‖) :=
      mul_le_mul hto hmap
        (norm_nonneg (mapAlgebraic 𝕜 E F E' F' f g)) zero_le_one
    _ ≤ 1 * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left hprod zero_le_one
    _ = ‖f‖ * ‖g‖ := one_mul _

end Functorial

end

end MathlibAnnex.ProjectiveTensorProduct
