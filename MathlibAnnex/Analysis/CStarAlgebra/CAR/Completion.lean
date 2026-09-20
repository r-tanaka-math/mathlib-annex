import MathlibAnnex.Analysis.CStarAlgebra.CAR.PureRoot
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Algebra.Star.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.CStarAlgebra.Projection

set_option autoImplicit false

open scoped ComplexOrder
open Set

namespace MathlibAnnex.CStarAlgebra.CAR

/-- The compatible embedding between arbitrary finite stages. -/
noncomputable def embed (n m : ℕ) (h : n ≤ m) : Stage n →⋆ₐ[ℂ] Stage m :=
  Nat.leRecOn h (fun {k} g => (step k).comp g) (StarAlgHom.id ℂ (Stage n))

@[simp]
theorem embed_refl (n : ℕ) : embed n n le_rfl = StarAlgHom.id ℂ (Stage n) := by
  unfold embed
  exact Nat.leRecOn_self _

@[simp]
theorem embed_succ (n m : ℕ) (h : n ≤ m) :
    embed n (m + 1) (Nat.le.step h) = (step m).comp (embed n m h) := by
  unfold embed
  exact Nat.leRecOn_succ h _

@[simp]
theorem embed_apply (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (x : Stage n),
    embed n m h x = Nat.leRecOn h (fun {k} y => step k y) x := by
  apply Nat.le_induction
  · intro x
    rw [embed_refl]
    exact (Nat.leRecOn_self x).symm
  · intro m h ih x
    rw [embed_succ, StarAlgHom.comp_apply, ih, Nat.leRecOn_succ h]
    exact h

theorem embed_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    embed i k (hij.trans hjk) = (embed j k hjk).comp (embed i j hij) := by
  apply StarAlgHom.ext
  intro x
  simp only [StarAlgHom.comp_apply, embed_apply]
  exact Nat.leRecOn_trans hij hjk x

noncomputable instance embedDirectedSystem :
    DirectedSystem Stage (fun _ _ h => embed _ _ h) where
  map_self {i} x := by rw [embed_refl]; rfl
  map_map {k j i} hij hjk x := by rw [← StarAlgHom.comp_apply, ← embed_trans]

/-- The algebraic union of all binary matrix stages. -/
abbrev AlgCAR := DirectLimit Stage (fun _ _ h => embed _ _ h)

theorem norm_embed (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (x : Stage n),
    ‖embed n m h x‖ = ‖x‖ := by
  apply Nat.le_induction
  · intro x
    rw [embed_refl]
    rfl
  · intro m h ih x
    rw [embed_succ, StarAlgHom.comp_apply, norm_step, ih]
    exact h

theorem embed_injective (n m : ℕ) (h : n ≤ m) : Function.Injective (embed n m h) :=
  fun x y hxy => by
    rw [← sub_eq_zero, ← norm_eq_zero, ← norm_embed n m h]
    simp only [map_sub, hxy, sub_self, norm_zero]

theorem isometry_step (n : ℕ) : Isometry (step n) :=
  AddMonoidHomClass.isometry_of_norm (step n) (norm_step n)

theorem isometry_stage : ∀ n, Isometry (fun x : Stage n => step n x) :=
  isometry_step

/-- The metric union of the finite CAR stages. -/
abbrev PreCAR := Metric.InductiveLimit isometry_stage

/-- The finite-stage map into the metric union. -/
noncomputable def toPreCAR (n : ℕ) : Stage n → PreCAR :=
  Metric.toInductiveLimit isometry_stage n

theorem isometry_toPreCAR (n : ℕ) : Isometry (toPreCAR n) :=
  Metric.toInductiveLimit_isometry isometry_stage n

@[simp]
theorem toPreCAR_step (n : ℕ) (x : Stage n) :
    toPreCAR (n + 1) (step n x) = toPreCAR n x := by
  exact congrFun (Metric.toInductiveLimit_commute isometry_stage n) x

theorem toPreCAR_embed (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (x : Stage n),
    toPreCAR m (embed n m h x) = toPreCAR n x := by
  apply Nat.le_induction
  · intro x
    rw [embed_refl]
    rfl
  · intro m h ih x
    rw [embed_succ, StarAlgHom.comp_apply, toPreCAR_step, ih]
    exact h

private theorem alg_compatible (x y : Σ n, Stage n)
    (hxy : @Inseparable _ (Metric.inductivePremetric isometry_stage).toUniformSpace.toTopologicalSpace
      x y) :
    (⟦x⟧ : AlgCAR) = ⟦y⟧ := by
  let m := max x.1 y.1
  have hx : x.1 ≤ m := le_max_left _ _
  have hy : y.1 ≤ m := le_max_right _ _
  have hdist : Metric.inductiveLimitDist (fun n x => step n x) x y = 0 :=
    (@Metric.inseparable_iff _ (Metric.inductivePremetric isometry_stage) x y).mp hxy
  have hd : dist (Nat.leRecOn hx (fun {k} z => step k z) x.2 : Stage m)
      (Nat.leRecOn hy (fun {k} z => step k z) y.2 : Stage m) = 0 := by
    rw [← Metric.inductiveLimitDist_eq_dist isometry_stage x y m hx hy]
    exact hdist
  have he : (Nat.leRecOn hx (fun {k} z => step k z) x.2 : Stage m) =
      (Nat.leRecOn hy (fun {k} z => step k z) y.2 : Stage m) := dist_eq_zero.mp hd
  apply Quotient.sound
  exact ⟨m, hx, hy, by simpa only [embed_apply] using he⟩

/-- Forget the metric presentation of the union. -/
noncomputable def preToAlg : PreCAR → AlgCAR :=
  @SeparationQuotient.lift _ _
    (Metric.inductivePremetric isometry_stage).toUniformSpace.toTopologicalSpace
    (fun x => (⟦x⟧ : AlgCAR)) alg_compatible

@[simp]
theorem preToAlg_toPreCAR (n : ℕ) (x : Stage n) :
    preToAlg (toPreCAR n x) = (⟦⟨n, x⟩⟧ : AlgCAR) := by
  rfl

/-- Recover the metric presentation from the algebraic direct limit. -/
noncomputable def algToPre : AlgCAR → PreCAR :=
  DirectLimit.lift (fun _ _ h => embed _ _ h) (fun n => toPreCAR n)
    (fun i j h x => (toPreCAR_embed i j h x).symm)

@[simp]
theorem algToPre_mk (n : ℕ) (x : Stage n) :
    algToPre (⟦⟨n, x⟩⟧ : AlgCAR) = toPreCAR n x := rfl

theorem algToPre_preToAlg (x : PreCAR) : algToPre (preToAlg x) = x := by
  obtain ⟨⟨n, y⟩, rfl⟩ := Quotient.exists_rep x
  rfl

theorem preToAlg_algToPre (x : AlgCAR) : preToAlg (algToPre x) = x := by
  obtain ⟨⟨n, y⟩, rfl⟩ := Quotient.exists_rep x
  rfl

/-- Algebraic and metric presentations of the stage union coincide. -/
noncomputable def preAlgEquiv : PreCAR ≃ AlgCAR where
  toFun := preToAlg
  invFun := algToPre
  left_inv := algToPre_preToAlg
  right_inv := preToAlg_algToPre

noncomputable instance preRing : Ring PreCAR := preAlgEquiv.ring

noncomputable instance preAlgebra : Algebra ℂ PreCAR := Equiv.algebra ℂ preAlgEquiv

noncomputable instance preStarRing : StarRing PreCAR := preAlgEquiv.starRing

noncomputable instance preStarModule : StarModule ℂ PreCAR := preAlgEquiv.starModule ℂ

/-- The equivalence between metric and algebraic unions respects all star-algebra operations. -/
noncomputable def preStarAlgEquiv : PreCAR ≃⋆ₐ[ℂ] AlgCAR where
  __ := Equiv.ringEquiv preAlgEquiv
  map_star' x := by
    change preToAlg (algToPre (star (preToAlg x))) = star (preToAlg x)
    exact preToAlg_algToPre _
  map_smul' r x := by
    simp [Equiv.smul_def]

/-- The canonical algebraic map of a finite stage into the algebraic union. -/
noncomputable def algStageHom (n : ℕ) : Stage n →⋆ₐ[ℂ] AlgCAR where
  __ := DirectLimit.Algebra.of Stage (fun _ _ h => embed _ _ h) n
  map_star' _ := rfl

/-- The canonical map of a finite stage into the metric union. -/
noncomputable def stageHom (n : ℕ) : Stage n →⋆ₐ[ℂ] PreCAR :=
  preStarAlgEquiv.symm.toStarAlgHom.comp (algStageHom n)

@[simp]
theorem stageHom_apply (n : ℕ) (x : Stage n) : stageHom n x = toPreCAR n x := by
  apply preAlgEquiv.injective
  rfl

theorem stageHom_injective (n : ℕ) : Function.Injective (stageHom n) :=
  fun x y h => (isometry_toPreCAR n).injective <| by simpa only [← stageHom_apply] using h

theorem exists_common_stage (x y : PreCAR) :
    ∃ n, ∃ a b : Stage n, stageHom n a = x ∧ stageHom n b = y := by
  obtain ⟨n, a, b, ha, hb⟩ :=
    DirectLimit.exists_eq_mk₂ (fun _ _ h => embed _ _ h) (preToAlg x) (preToAlg y)
  refine ⟨n, a, b, ?_, ?_⟩
  · apply preAlgEquiv.injective
    exact ha.symm
  · apply preAlgEquiv.injective
    exact hb.symm

noncomputable instance preNorm : Norm PreCAR where
  norm x := dist x 0

@[simp]
theorem norm_stageHom (n : ℕ) (x : Stage n) : ‖stageHom n x‖ = ‖x‖ := by
  rw [stageHom_apply]
  change dist (toPreCAR n x) 0 = ‖x‖
  rw [← map_zero (stageHom n), stageHom_apply, (isometry_toPreCAR n).dist_eq]
  exact dist_zero_right x

noncomputable instance preNormedAddCommGroup : NormedAddCommGroup PreCAR where
  toNorm := preNorm
  toAddCommGroup := preRing.toAddCommGroup
  toMetricSpace := Metric.instMetricSpaceInductiveLimit
  dist_eq x y := by
    obtain ⟨n, a, b, rfl, rfl⟩ := exists_common_stage x y
    rw [← map_neg, ← map_add, norm_stageHom]
    calc
      dist ((stageHom n) a) ((stageHom n) b) = dist a b := by
        simpa only [stageHom_apply] using (isometry_toPreCAR n).dist_eq a b
      _ = ‖-a + b‖ := NormedAddGroup.dist_eq a b

noncomputable instance preNormedRing : NormedRing PreCAR where
  __ := preNormedAddCommGroup
  __ := preRing
  norm_mul_le x y := by
    obtain ⟨n, a, b, rfl, rfl⟩ := exists_common_stage x y
    simpa only [← map_mul, norm_stageHom] using norm_mul_le a b

noncomputable instance preNormedSpace : NormedSpace ℂ PreCAR where
  norm_smul_le c x := by
    obtain ⟨n, a, b, ha, _⟩ := exists_common_stage x x
    rw [← ha]
    calc
      ‖c • stageHom n a‖ = ‖stageHom n (c • a)‖ := by rw [map_smul]
      _ = ‖c • a‖ := norm_stageHom n _
      _ ≤ ‖c‖ * ‖a‖ := norm_smul_le c a
      _ = ‖c‖ * ‖stageHom n a‖ := by rw [norm_stageHom]

noncomputable instance preNormedAlgebra : NormedAlgebra ℂ PreCAR where
  __ := preAlgebra
  norm_smul_le := preNormedSpace.norm_smul_le

noncomputable instance preCStarRing : CStarRing PreCAR where
  norm_mul_self_le x := by
    obtain ⟨n, a, b, ha, _⟩ := exists_common_stage x x
    rw [← ha]
    simpa only [← map_star, ← map_mul, norm_stageHom] using
      (CStarRing.norm_mul_self_le a)

noncomputable instance preSeparableSpace : TopologicalSpace.SeparableSpace PreCAR :=
  Metric.separableSpaceInductiveLimit_of_separableSpace isometry_stage

theorem dense_stageUnion : Dense (⋃ n, Set.range (stageHom n)) := by
  let current : MetricSpace PreCAR := inferInstance
  let original : MetricSpace PreCAR := Metric.instMetricSpaceInductiveLimit
  have hmetric : current = original := MetricSpace.ext (by rfl)
  change @Dense PreCAR current.toUniformSpace.toTopologicalSpace
    (⋃ n, Set.range (stageHom n))
  rw [hmetric]
  have hrange (n : ℕ) : Set.range (stageHom n) =
      Set.range (Metric.toInductiveLimit isometry_stage n) := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩
    · exact ⟨x, stageHom_apply n x⟩
    · exact ⟨x, (stageHom_apply n x).symm⟩
  rw [show (⋃ n, Set.range (stageHom n)) =
      ⋃ n, Set.range (Metric.toInductiveLimit isometry_stage n) by
    apply congrArg (fun f : ℕ → Set PreCAR => ⋃ n, f n)
    funext n
    exact hrange n]
  exact Metric.dense_iUnion_range_toInductiveLimit isometry_stage

noncomputable instance preNontrivial : Nontrivial PreCAR :=
  ⟨⟨stageHom 0 0, stageHom 0 1, fun h => zero_ne_one (stageHom_injective 0 h)⟩⟩

/-- The norm completion of the binary matrix-stage union. -/
abbrev Limit := UniformSpace.Completion PreCAR

private theorem limit_norm_smul_le (c : ℂ) (x : Limit) :
    ‖c • x‖ ≤ ‖c‖ * ‖x‖ := norm_smul_le c x

noncomputable instance limitNormedAlgebra : NormedAlgebra ℂ Limit where
  toAlgebra := (inferInstance : Algebra ℂ Limit)
  norm_smul_le := limit_norm_smul_le

noncomputable instance limitStar : Star Limit where
  star x := UniformSpace.Completion.map (star : PreCAR → PreCAR) x

@[simp]
theorem star_coe (x : PreCAR) : star (x : Limit) = (star x : PreCAR) :=
  UniformSpace.Completion.map_coe star_isometry.uniformContinuous x

theorem continuous_limit_star : Continuous (star : Limit → Limit) :=
  UniformSpace.Completion.continuous_map

noncomputable instance limitContinuousStar : ContinuousStar Limit :=
  ⟨continuous_limit_star⟩

noncomputable instance limitStarRing : StarRing Limit where
  star_involutive x := by
    refine UniformSpace.Completion.induction_on (α := PreCAR)
      (p := fun x => star (star x) = x) x ?_ ?_
    · apply isClosed_eq <;> fun_prop
    · intro a
      simp only [star_coe, star_star]
  star_add x y := by
    refine UniformSpace.Completion.induction_on₂ (α := PreCAR) (β := PreCAR)
      (p := fun x y => star (x + y) = star x + star y) x y ?_ ?_
    · apply isClosed_eq <;> fun_prop
    · intro a b
      simp only [← UniformSpace.Completion.coe_add, star_coe, star_add]
  star_mul x y := by
    refine UniformSpace.Completion.induction_on₂ (α := PreCAR) (β := PreCAR)
      (p := fun x y => star (x * y) = star y * star x) x y ?_ ?_
    · apply isClosed_eq <;> fun_prop
    · intro a b
      simp only [← UniformSpace.Completion.coe_mul, star_coe, star_mul]

noncomputable instance limitStarModule : StarModule ℂ Limit where
  star_smul c x := by
    refine UniformSpace.Completion.induction_on (α := PreCAR)
      (p := fun x => star (c • x) = star c • star x) x ?_ ?_
    · exact isClosed_eq
        (continuous_limit_star.comp (continuous_const_smul c))
        ((continuous_const_smul (star c)).comp continuous_limit_star)
    · intro a
      simp only [← UniformSpace.Completion.coe_smul, star_coe, star_smul]

noncomputable instance limitCStarRing : CStarRing Limit where
  norm_mul_self_le x := by
    refine UniformSpace.Completion.induction_on (α := PreCAR)
      (p := fun x => ‖x‖ * ‖x‖ ≤ ‖star x * x‖) x ?_ ?_
    · exact isClosed_le (continuous_norm.mul continuous_norm)
        (continuous_norm.comp (continuous_limit_star.mul continuous_id))
    · intro a
      simpa only [← UniformSpace.Completion.coe_mul, star_coe,
        UniformSpace.Completion.norm_coe] using CStarRing.norm_mul_self_le a

noncomputable instance limitCStarAlgebra : CStarAlgebra Limit where
  toNormedRing := (inferInstance : NormedRing Limit)
  toStarRing := limitStarRing
  toCompleteSpace := (inferInstance : CompleteSpace Limit)
  toCStarRing := limitCStarRing
  toNormedAlgebra := limitNormedAlgebra
  toStarModule := limitStarModule

noncomputable instance limitPartialOrder : PartialOrder Limit :=
  CStarAlgebra.spectralOrder Limit

noncomputable instance limitStarOrderedRing : StarOrderedRing Limit :=
  CStarAlgebra.spectralOrderedRing Limit

noncomputable instance limitNontrivial : Nontrivial Limit :=
  ⟨⟨((0 : PreCAR) : Limit), ((1 : PreCAR) : Limit), fun h =>
    zero_ne_one (UniformSpace.Completion.coe_injective PreCAR h)⟩⟩

/-- The canonical dense star-algebra map into the completion. -/
noncomputable def toLimit : PreCAR →⋆ₐ[ℂ] Limit where
  toFun x := (x : Limit)
  map_one' := UniformSpace.Completion.coe_one PreCAR
  map_mul' := UniformSpace.Completion.coe_mul
  map_zero' := UniformSpace.Completion.coe_zero
  map_add' := UniformSpace.Completion.coe_add
  commutes' _ := rfl
  map_star' x := (star_coe x).symm

/-- The compatible isometric embedding of the `n`-th matrix stage into the completed CAR algebra. -/
noncomputable def ofStage (n : ℕ) : Stage n →⋆ₐ[ℂ] Limit :=
  toLimit.comp (stageHom n)

@[simp]
theorem ofStage_apply (n : ℕ) (x : Stage n) :
    ofStage n x = (stageHom n x : Limit) := rfl

@[simp]
theorem norm_ofStage (n : ℕ) (x : Stage n) : ‖ofStage n x‖ = ‖x‖ := by
  rw [ofStage_apply, UniformSpace.Completion.norm_coe, norm_stageHom]

theorem ofStage_injective (n : ℕ) : Function.Injective (ofStage n) :=
  AddMonoidHomClass.isometry_of_norm (ofStage n) (norm_ofStage n) |>.injective

@[simp]
theorem ofStage_step (n : ℕ) (x : Stage n) :
    ofStage (n + 1) (step n x) = ofStage n x := by
  simp only [ofStage_apply, stageHom_apply, toPreCAR_step]

theorem dense_stageRange : Dense (⋃ n, Set.range (ofStage n)) := by
  let U : Set PreCAR := ⋃ n, Set.range (stageHom n)
  let V : Set Limit := ⋃ n, Set.range (ofStage n)
  have himage : ((fun x : PreCAR => (x : Limit)) '' U) ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    rcases hn with ⟨a, rfl⟩
    exact Set.mem_iUnion.2 ⟨n, ⟨a, rfl⟩⟩
  have hrange : Set.range (fun x : PreCAR => (x : Limit)) ⊆ closure V :=
    let hcont : Continuous (fun x : PreCAR => (x : Limit)) :=
      UniformSpace.Completion.continuous_coe PreCAR
    (hcont.range_subset_closure_image_dense dense_stageUnion).trans (closure_mono himage)
  exact Dense.of_closure (UniformSpace.Completion.denseRange_coe.mono hrange)

noncomputable instance limitSeparableSpace : TopologicalSpace.SeparableSpace Limit :=
  UniformSpace.Completion.separableSpace_completion

theorem finrank_stage (n : ℕ) :
    Module.finrank ℂ (Stage n) = (2 ^ n) * (2 ^ n) := by
  change Module.finrank ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) = _
  rw [Module.finrank_matrix]
  simp

theorem not_finiteDimensional : ¬ FiniteDimensional ℂ Limit := by
  intro hfinite
  let k := Module.finrank ℂ Limit
  let n := k + 1
  have hle : Module.finrank ℂ (Stage n) ≤ k :=
    (ofStage n).toLinearMap.finrank_le_finrank_of_injective (ofStage_injective n)
  have hkpow : k < 2 ^ n := by
    exact (Nat.lt_succ_self k).trans n.lt_two_pow_self
  have hpowsq : 2 ^ n ≤ (2 ^ n) * (2 ^ n) :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))
  rw [finrank_stage] at hle
  exact (Nat.not_lt_of_ge hle) (hkpow.trans_le hpowsq)

@[simp]
theorem rootFunctional_embed (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (x : Stage n),
    rootFunctional m (embed n m h x) = rootFunctional n x := by
  apply Nat.le_induction
  · intro x
    rw [embed_refl]
    rfl
  · intro m h ih x
    rw [embed_succ, StarAlgHom.comp_apply, rootFunctional_step, ih]
    exact h

/-- The compatible root-coordinate functional on the algebraic stage union. -/
noncomputable def algRootLinear : AlgCAR →ₗ[ℂ] ℂ :=
  DirectLimit.Module.lift ℂ ℕ Stage (fun _ _ h => embed _ _ h)
    (fun n => (rootFunctional n).toLinearMap)
    (fun i j hij x => rootFunctional_embed i j hij x)

@[simp]
theorem algRootLinear_stage (n : ℕ) (x : Stage n) :
    algRootLinear (algStageHom n x) = rootFunctional n x := rfl

/-- The root-coordinate functional on the normed stage union. -/
noncomputable def preRootLinear : PreCAR →ₗ[ℂ] ℂ :=
  algRootLinear.comp preStarAlgEquiv.toAlgEquiv.toLinearEquiv.toLinearMap

@[simp]
theorem preRootLinear_stage (n : ℕ) (x : Stage n) :
    preRootLinear (stageHom n x) = rootFunctional n x := rfl

theorem norm_preRootLinear_le (x : PreCAR) : ‖preRootLinear x‖ ≤ ‖x‖ := by
  obtain ⟨n, a, b, ha, _⟩ := exists_common_stage x x
  rw [← ha, preRootLinear_stage, norm_stageHom]
  simpa [rootFunctional_apply] using
    (CStarMatrix.norm_entry_le_norm (M := a) (i := (0 : Fin (2 ^ n)))
      (j := (0 : Fin (2 ^ n))))

/-- The bounded root-coordinate functional before completion. -/
noncomputable def preRootFunctional : PreCAR →L[ℂ] ℂ :=
  preRootLinear.mkContinuous 1 fun x => by simpa using norm_preRootLinear_le x

@[simp]
theorem preRootFunctional_stage (n : ℕ) (x : Stage n) :
    preRootFunctional (stageHom n x) = rootFunctional n x := rfl

/-- The product-vector state candidate on the completed CAR algebra. -/
noncomputable def rootState : Limit →L[ℂ] ℂ :=
  preRootFunctional.extend (UniformSpace.Completion.toComplL : PreCAR →L[ℂ] Limit)

@[simp]
theorem rootState_coe (x : PreCAR) : rootState (x : Limit) = preRootFunctional x := by
  exact ContinuousLinearMap.extend_eq preRootFunctional
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe PreCAR) x

@[simp]
theorem rootState_stage (n : ℕ) (x : Stage n) :
    rootState (ofStage n x) = rootFunctional n x := by
  rw [ofStage_apply, rootState_coe, preRootFunctional_stage]

theorem preRootFunctional_star_mul_self_nonneg (x : PreCAR) :
    0 ≤ preRootFunctional (star x * x) := by
  obtain ⟨n, a, b, ha, _⟩ := exists_common_stage x x
  rw [← ha, ← map_star, ← map_mul, preRootFunctional_stage]
  exact rootLinear_nonneg n (star a * a) (star_mul_self_nonneg a)

theorem rootState_star_mul_self_nonneg (x : Limit) :
    0 ≤ rootState (star x * x) := by
  refine UniformSpace.Completion.induction_on (α := PreCAR)
    (p := fun x => 0 ≤ rootState (star x * x)) x ?_ ?_
  · exact isClosed_le continuous_const
      (rootState.continuous.comp (continuous_limit_star.mul continuous_id))
  · intro a
    simpa only [← UniformSpace.Completion.coe_mul, star_coe, rootState_coe] using
      preRootFunctional_star_mul_self_nonneg a

theorem rootState_nonneg (x : Limit) (hx : 0 ≤ x) : 0 ≤ rootState x := by
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx with ⟨y, rfl⟩
  exact rootState_star_mul_self_nonneg y

@[simp]
theorem rootState_one : rootState (1 : Limit) = 1 := by
  have hone : ofStage 0 (1 : Stage 0) = (1 : Limit) := map_one (ofStage 0)
  rw [← hone, rootState_stage]
  exact rootPositiveFunctional_one 0

theorem rootState_mem_stateSpace : rootState ∈ MathlibAnnex.CStarAlgebra.stateSpace Limit :=
  ⟨rootState_nonneg, rootState_one⟩

/-- Restriction of a continuous functional to a finite stage. -/
noncomputable def restrictState (n : ℕ) (phi : Limit →L[ℂ] ℂ) : Stage n →L[ℂ] ℂ :=
  phi.comp ((ofStage n).toLinearMap.mkContinuous 1 fun x => by
    simpa using (le_of_eq (norm_ofStage n x)))

@[simp]
theorem restrictState_apply (n : ℕ) (phi : Limit →L[ℂ] ℂ) (x : Stage n) :
    restrictState n phi x = phi (ofStage n x) := rfl

theorem restrictState_mem_stateSpace (n : ℕ) (phi : Limit →L[ℂ] ℂ)
    (hphi : phi ∈ MathlibAnnex.CStarAlgebra.stateSpace Limit) :
    restrictState n phi ∈ MathlibAnnex.CStarAlgebra.stateSpace (Stage n) := by
  constructor
  · intro x hx
    letI : NonnegSpectrumClass ℝ (Stage n) :=
      CStarAlgebra.instNonnegSpectrumClass'
    letI : NonUnitalContinuousFunctionalCalculus ℂ (Stage n) IsStarNormal :=
      (IsStarNormal.instNonUnitalContinuousFunctionalCalculus
        (A := Stage n)).toNonUnitalContinuousFunctionalCalculus
    letI : NonUnitalContinuousFunctionalCalculus ℝ (Stage n) IsSelfAdjoint :=
      IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx with ⟨y, rfl⟩
    change 0 ≤ phi (ofStage n (star y * y))
    apply hphi.1
    simpa only [map_mul, map_star] using star_mul_self_nonneg (ofStage n y)
  · rw [restrictState_apply, map_one, hphi.2]

theorem eq_rootState_of_restrict (phi : Limit →L[ℂ] ℂ)
    (hphi : ∀ n, restrictState n phi = rootFunctional n) : phi = rootState := by
  apply ContinuousLinearMap.coeFn_injective
  exact phi.continuous.ext_on dense_stageRange rootState.continuous fun x hx => by
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    rcases hn with ⟨a, rfl⟩
    calc
      phi (ofStage n a) = restrictState n phi a := rfl
      _ = rootFunctional n a := DFunLike.congr_fun (hphi n) a
      _ = rootState (ofStage n a) := (rootState_stage n a).symm

/-- The completed product-vector state is pure, proved from its pure finite restrictions. -/
theorem isPureState_rootState : MathlibAnnex.CStarAlgebra.IsPureState Limit rootState := by
  rw [MathlibAnnex.CStarAlgebra.IsPureState, mem_extremePoints_iff_left]
  refine ⟨rootState_mem_stateSpace, ?_⟩
  intro phi₁ hphi₁ phi₂ hphi₂ hsegment
  rcases hsegment with ⟨a, b, ha, hb, hab, hcomb⟩
  apply eq_rootState_of_restrict phi₁
  intro n
  have hcomb_n : a • restrictState n phi₁ + b • restrictState n phi₂ =
      rootFunctional n := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun psi : Limit →L[ℂ] ℂ => psi (ofStage n x)) hcomb
    calc
      (a • restrictState n phi₁ + b • restrictState n phi₂) x =
          (a • phi₁ + b • phi₂) (ofStage n x) := rfl
      _ = rootState (ofStage n x) := hx
      _ = rootFunctional n x := rootState_stage n x
  have hpure := isPureState_rootFunctional n
  rw [MathlibAnnex.CStarAlgebra.IsPureState, mem_extremePoints_iff_left] at hpure
  exact hpure.2 (restrictState n phi₁)
    (restrictState_mem_stateSpace n phi₁ hphi₁)
    (restrictState n phi₂) (restrictState_mem_stateSpace n phi₂ hphi₂)
    ⟨a, b, ha, hb, hab, hcomb_n⟩

theorem step_rootProjection_mul (n : ℕ) :
    step n (rootProjection n) * rootProjection (n + 1) = rootProjection (n + 1) := by
  let p := rootProjection (n + 1)
  let q := step n (rootProjection n)
  have hp : IsStarProjection p := isStarProjection_rootProjection (n + 1)
  have hq : IsStarProjection q := (isStarProjection_rootProjection n).map (step n)
  have hentry : rootFunctional (n + 1) q = 1 := by
    change rootFunctional (n + 1) (step n (rootProjection n)) = 1
    rw [rootFunctional_step, rootFunctional_apply]
    simp [rootProjection]
  have hsand : p * q * p = p := by
    calc
      p * q * p = rootFunctional (n + 1) q • p := rootProjection_mul_mul (n + 1) q
      _ = p := by rw [hentry, one_smul]
  have hz : star (q * p - p) * (q * p - p) = 0 := by
    rw [star_sub, star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    noncomm_ring [hp.isIdempotentElem.eq, hsand]
    rw [← mul_assoc q q p, hq.isIdempotentElem.eq]
    simp
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)

/-- The common root flag in the completed CAR algebra. -/
noncomputable def rootFlag (n : ℕ) : Limit :=
  ofStage n (rootProjection n)

@[simp]
theorem rootFlag_zero : rootFlag 0 = 1 := by
  rw [rootFlag]
  have hp : rootProjection 0 = (1 : Stage 0) := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i
    fin_cases j
    simp [rootProjection]
  rw [hp, map_one]

theorem isStarProjection_rootFlag (n : ℕ) : IsStarProjection (rootFlag n) :=
  (isStarProjection_rootProjection n).map (ofStage n)

@[simp]
theorem rootState_rootFlag (n : ℕ) : rootState (rootFlag n) = 1 := by
  rw [rootFlag, rootState_stage, rootFunctional_apply]
  simp [rootProjection]

theorem rootFlag_succ_le (n : ℕ) : rootFlag (n + 1) ≤ rootFlag n := by
  apply (isStarProjection_rootFlag (n + 1)).le_iff_mul_eq_right
    (isStarProjection_rootFlag n) |>.2
  change ofStage n (rootProjection n) * ofStage (n + 1) (rootProjection (n + 1)) =
    ofStage (n + 1) (rootProjection (n + 1))
  rw [← ofStage_step n (rootProjection n), ← map_mul]
  exact congrArg (ofStage (n + 1)) (step_rootProjection_mul n)

theorem antitone_rootFlag : Antitone rootFlag :=
  antitone_nat_of_succ_le rootFlag_succ_le

@[simp]
theorem ofStage_embed (n m : ℕ) (h : n ≤ m) (x : Stage n) :
    ofStage m (embed n m h x) = ofStage n x := by
  simp only [ofStage_apply, stageHom_apply, toPreCAR_embed]

/-- Every finite-stage element has exact root compression at every later flag projection. -/
theorem rootFlag_mul_ofStage_mul (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    rootFlag n * ofStage m x * rootFlag n =
      rootState (ofStage m x) • rootFlag n := by
  rw [← ofStage_embed m n h x]
  change ofStage n (rootProjection n) * ofStage n (embed m n h x) *
      ofStage n (rootProjection n) =
    rootState (ofStage n (embed m n h x)) • ofStage n (rootProjection n)
  rw [← map_mul, ← map_mul, rootProjection_mul_mul, map_smul,
    rootState_stage]
  rfl

/-- The norm-valued root-compression error. -/
noncomputable def compressionError (n : ℕ) (x : Limit) : Limit :=
  rootFlag n * x * rootFlag n - rootState x • rootFlag n

theorem compressionError_sub (n : ℕ) (x y : Limit) :
    compressionError n x - compressionError n y = compressionError n (x - y) := by
  simp only [compressionError, map_sub, sub_smul]
  noncomm_ring

theorem norm_compressionError_le (n : ℕ) (x : Limit) :
    ‖compressionError n x‖ ≤ (1 + ‖rootState‖) * ‖x‖ := by
  have hq := (isStarProjection_rootFlag n).norm_le
  have hleft : ‖rootFlag n * x * rootFlag n‖ ≤ ‖x‖ := by
    calc
      ‖rootFlag n * x * rootFlag n‖ ≤ ‖rootFlag n‖ * ‖x‖ * ‖rootFlag n‖ := by
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          (norm_nonneg _))
      _ ≤ 1 * ‖x‖ * 1 := by gcongr
      _ = ‖x‖ := by ring
  have hright : ‖rootState x • rootFlag n‖ ≤ ‖rootState‖ * ‖x‖ := by
    rw [norm_smul]
    calc
      ‖rootState x‖ * ‖rootFlag n‖ ≤ (‖rootState‖ * ‖x‖) * 1 := by
        gcongr
        exact rootState.le_opNorm x
      _ = ‖rootState‖ * ‖x‖ := mul_one _
  calc
    ‖compressionError n x‖ ≤
        ‖rootFlag n * x * rootFlag n‖ + ‖rootState x • rootFlag n‖ := norm_sub_le _ _
    _ ≤ ‖x‖ + ‖rootState‖ * ‖x‖ := add_le_add hleft hright
    _ = (1 + ‖rootState‖) * ‖x‖ := by ring

theorem compressionError_ofStage (m n : ℕ) (h : m ≤ n) (x : Stage m) :
    compressionError n (ofStage m x) = 0 := by
  rw [compressionError, rootFlag_mul_ofStage_mul m n h x, sub_self]

/-- Root compression converges in norm for every element of the completed CAR algebra. -/
theorem tendsto_norm_compressionError (x : Limit) :
    Filter.Tendsto (fun n => ‖compressionError n x‖) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hden : 0 < ‖rootState‖ + 2 := by positivity
  obtain ⟨y, hy, hyx⟩ := dense_stageRange.exists_dist_lt x (div_pos hε hden)
  rcases Set.mem_iUnion.mp hy with ⟨m, hm⟩
  rcases hm with ⟨a, rfl⟩
  refine ⟨m, fun n hn => ?_⟩
  have hzero : compressionError n (ofStage m a) = 0 :=
    compressionError_ofStage m n hn a
  have hdist : ‖x - ofStage m a‖ < ε / (‖rootState‖ + 2) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hyx
  have hlarge : (‖rootState‖ + 2) * ‖x - ofStage m a‖ < ε := by
    rw [mul_comm]
    exact (lt_div_iff₀ hden).mp hdist
  have hcoeff : 1 + ‖rootState‖ ≤ ‖rootState‖ + 2 := by linarith
  have herr : ‖compressionError n x‖ < ε := by
    calc
      ‖compressionError n x‖ =
          ‖compressionError n x - compressionError n (ofStage m a)‖ := by rw [hzero, sub_zero]
      _ = ‖compressionError n (x - ofStage m a)‖ := by rw [compressionError_sub]
      _ ≤ (1 + ‖rootState‖) * ‖x - ofStage m a‖ := norm_compressionError_le n _
      _ ≤ (‖rootState‖ + 2) * ‖x - ofStage m a‖ := by
        gcongr
      _ < ε := hlarge
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using herr

end MathlibAnnex.CStarAlgebra.CAR
