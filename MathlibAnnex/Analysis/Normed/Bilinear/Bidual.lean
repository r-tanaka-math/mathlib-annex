import Mathlib.Analysis.Normed.Operator.Completeness
import MathlibAnnex.Analysis.Normed.Operator.WeakCompact

/-!
# Bidual extensions of bounded bilinear forms

The two Arens extensions of a bounded scalar-valued bilinear form are
constructed explicitly. Their equality is characterized by weak compactness
of the associated operator, and equivalently by existence of a separately
weak-star continuous extension.

`BidualModel` is a universe lift of the ordinary strong bidual. It is used
only to stabilize bundled operator-norm instances in the pinned Mathlib
release; `BidualForm.eval` evaluates on the actual strong biduals, and
`bidualModelEquiv` is a linear isometry onto them. Thus no alternative norm
or alternative bidual is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Topology WeakDual

namespace MathlibAnnex.BidualBilinear

universe uK uE uF uG

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

open MathlibAnnex.FiniteApproximation MathlibAnnex.WeakCompact

/-- A typeclass-stable presentation of the ordinary strong bidual. -/
abbrev BidualModel (𝕜 : Type uK) [RCLike 𝕜]
    (G : Type uG) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :=
  ULift.{0} (StrongDual 𝕜 (StrongDual 𝕜 G))

noncomputable instance bidualModelNormedAddCommGroup
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (BidualModel 𝕜 G) :=
  ULift.normedAddCommGroup

noncomputable instance bidualModelNormedSpace
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (BidualModel 𝕜 G) :=
  ULift.normedSpace

/-- The model is linearly isometric to the actual strong bidual. -/
def bidualModelEquiv
    (𝕜 : Type uK) [RCLike 𝕜]
    (G : Type uG) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    BidualModel 𝕜 G ≃ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 G) :=
  LinearIsometryEquiv.ulift 𝕜 _

/-- Bounded bilinear forms on the actual biduals, bundled through the
linearly isometric `BidualModel`. -/
abbrev BidualForm (𝕜 : Type uK) [RCLike 𝕜]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  BidualModel 𝕜 E →L[𝕜] BidualModel 𝕜 F →L[𝕜] 𝕜

namespace BidualForm

/-- Evaluate a bundled bidual form on the ordinary strong biduals. -/
def eval (C : BidualForm 𝕜 E F)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) : 𝕜 :=
  C (ULift.up x) (ULift.up y)

@[ext]
theorem ext {C D : BidualForm 𝕜 E F}
    (h : ∀ x y, eval C x y = eval D x y) : C = D := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simpa [eval] using h x.down y.down

end BidualForm

/-- The transposed curried form. -/
def transpose (B : E →L[𝕜] F →L[𝕜] 𝕜) : F →L[𝕜] E →L[𝕜] 𝕜 :=
  ContinuousLinearMap.flip B

@[simp]
theorem transpose_apply (B : E →L[𝕜] F →L[𝕜] 𝕜) (y : F) (x : E) :
    transpose B y x = B x y := rfl

@[simp]
theorem norm_transpose (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ‖transpose B‖ = ‖B‖ :=
  ContinuousLinearMap.opNorm_flip B

private theorem norm_dualMap_le {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) : ‖dualMap T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun g ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg T) (norm_nonneg g)) fun x ↦ ?_
  calc
    ‖g (T x)‖ ≤ ‖g‖ * ‖T x‖ := g.le_opNorm _
    _ ≤ ‖g‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg g)
    _ = (‖T‖ * ‖g‖) * ‖x‖ := by ring

private def firstArensLinear (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    BidualModel 𝕜 E →ₗ[𝕜] BidualModel 𝕜 F →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂ 𝕜
    (fun x y ↦ x.down (dualMap B y.down))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

/-- The first Arens extension `(x**,y**) ↦ x** (B* y**)`. -/
def firstArens (B : E →L[𝕜] F →L[𝕜] 𝕜) : BidualForm 𝕜 E F :=
  (firstArensLinear B).mkContinuous₂ ‖B‖ fun x y ↦ by
    calc
      ‖x.down (dualMap B y.down)‖ ≤ ‖x.down‖ * ‖dualMap B y.down‖ :=
        x.down.le_opNorm _
      _ ≤ ‖x.down‖ * (‖dualMap B‖ * ‖y.down‖) :=
        mul_le_mul_of_nonneg_left ((dualMap B).le_opNorm y.down)
          (norm_nonneg x.down)
      _ ≤ ‖x.down‖ * (‖B‖ * ‖y.down‖) := by
        gcongr
        exact norm_dualMap_le B
      _ = ‖B‖ * ‖x‖ * ‖y‖ := by
        change ‖x‖ * (‖B‖ * ‖y‖) = _
        ring

@[simp]
theorem firstArens_apply (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    BidualForm.eval (firstArens B) x y = x (dualMap B y) := rfl

private def secondArensLinear (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    BidualModel 𝕜 E →ₗ[𝕜] BidualModel 𝕜 F →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂ 𝕜
    (fun x y ↦ y.down (dualMap (transpose B) x.down))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

/-- The second Arens extension `(x**,y**) ↦ y** ((Bᵗ)* x**)`. -/
def secondArens (B : E →L[𝕜] F →L[𝕜] 𝕜) : BidualForm 𝕜 E F :=
  (secondArensLinear B).mkContinuous₂ ‖B‖ fun x y ↦ by
    calc
      ‖y.down (dualMap (transpose B) x.down)‖ ≤
          ‖y.down‖ * ‖dualMap (transpose B) x.down‖ :=
        y.down.le_opNorm _
      _ ≤ ‖y.down‖ * (‖dualMap (transpose B)‖ * ‖x.down‖) :=
        mul_le_mul_of_nonneg_left
          ((dualMap (transpose B)).le_opNorm x.down) (norm_nonneg y.down)
      _ ≤ ‖y.down‖ * (‖transpose B‖ * ‖x.down‖) := by
        gcongr
        exact norm_dualMap_le (transpose B)
      _ = ‖B‖ * ‖x‖ * ‖y‖ := by
        rw [norm_transpose]
        change ‖y‖ * (‖B‖ * ‖x‖) = _
        ring

@[simp]
theorem secondArens_apply (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (x : StrongDual 𝕜 (StrongDual 𝕜 E))
    (y : StrongDual 𝕜 (StrongDual 𝕜 F)) :
    BidualForm.eval (secondArens B) x y =
      y (dualMap (transpose B) x) := rfl

@[simp]
theorem firstArens_canonical (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (x : E) (y : F) :
    BidualForm.eval (firstArens B)
      (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) = B x y := rfl

@[simp]
theorem secondArens_canonical (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (x : E) (y : F) :
    BidualForm.eval (secondArens B)
      (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) = B x y := rfl

private theorem norm_firstArens_le (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ‖firstArens B‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

private theorem norm_secondArens_le (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ‖secondArens B‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

private theorem norm_le_of_extends
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (C : BidualForm 𝕜 E F)
    (hC : ∀ x y, BidualForm.eval C
      (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y) = B x y) :
    ‖B‖ ≤ ‖C‖ := by
  refine ContinuousLinearMap.opNorm_le_bound B (norm_nonneg C) fun x ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound (B x)
    (mul_nonneg (norm_nonneg C) (norm_nonneg x)) fun y ↦ ?_
  rw [← hC x y]
  have h := C.le_opNorm₂
    (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 E x))
    (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 F y))
  change ‖BidualForm.eval C
      (NormedSpace.inclusionInDoubleDual 𝕜 E x)
      (NormedSpace.inclusionInDoubleDual 𝕜 F y)‖ ≤
    ‖C‖ * ‖NormedSpace.inclusionInDoubleDual 𝕜 E x‖ *
      ‖NormedSpace.inclusionInDoubleDual 𝕜 F y‖ at h
  have hxnorm : ‖NormedSpace.inclusionInDoubleDual 𝕜 E x‖ = ‖x‖ := by
    exact (NormedSpace.inclusionInDoubleDualLi
      (𝕜 := 𝕜) (E := E)).norm_map x
  have hynorm : ‖NormedSpace.inclusionInDoubleDual 𝕜 F y‖ = ‖y‖ := by
    exact (NormedSpace.inclusionInDoubleDualLi
      (𝕜 := 𝕜) (E := F)).norm_map y
  rwa [hxnorm, hynorm] at h

@[simp]
theorem norm_firstArens (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ‖firstArens B‖ = ‖B‖ := by
  apply le_antisymm (norm_firstArens_le B)
  exact norm_le_of_extends B (firstArens B) (firstArens_canonical B)

@[simp]
theorem norm_secondArens (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ‖secondArens B‖ = ‖B‖ := by
  apply le_antisymm (norm_secondArens_le B)
  exact norm_le_of_extends B (secondArens B) (secondArens_canonical B)

/-- Weak-star continuity in the first variable, on the actual bidual. -/
def ContinuousFirst (C : BidualForm 𝕜 E F) : Prop :=
  ∀ y, Continuous fun x : WeakDual 𝕜 (StrongDual 𝕜 E) ↦
    BidualForm.eval C (WeakDual.toStrongDual x) y

/-- Weak-star continuity in the second variable, on the actual bidual. -/
def ContinuousSecond (C : BidualForm 𝕜 E F) : Prop :=
  ∀ x, Continuous fun y : WeakDual 𝕜 (StrongDual 𝕜 F) ↦
    BidualForm.eval C x (WeakDual.toStrongDual y)

def SeparatelyWeakStarContinuous (C : BidualForm 𝕜 E F) : Prop :=
  ContinuousFirst C ∧ ContinuousSecond C

def Extends (B : E →L[𝕜] F →L[𝕜] 𝕜)
    (C : BidualForm 𝕜 E F) : Prop :=
  ∀ x y, BidualForm.eval C
    (NormedSpace.inclusionInDoubleDual 𝕜 E x)
    (NormedSpace.inclusionInDoubleDual 𝕜 F y) = B x y

theorem continuousFirst_firstArens (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ContinuousFirst (firstArens B) := by
  intro y
  exact WeakDual.eval_continuous (dualMap B y)

theorem continuousSecond_secondArens (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    ContinuousSecond (secondArens B) := by
  intro x
  exact WeakDual.eval_continuous (dualMap (transpose B) x)

private theorem continuousSecond_firstArens_canonical
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (x : E) :
    Continuous fun y : WeakDual 𝕜 (StrongDual 𝕜 F) ↦
      BidualForm.eval (firstArens B)
        (NormedSpace.inclusionInDoubleDual 𝕜 E x)
        (WeakDual.toStrongDual y) := by
  change Continuous fun y : WeakDual 𝕜 (StrongDual 𝕜 F) ↦ y (B x)
  exact WeakDual.eval_continuous (B x)

private theorem continuousFirst_secondArens_canonical
    (B : E →L[𝕜] F →L[𝕜] 𝕜) (y : F) :
    Continuous fun x : WeakDual 𝕜 (StrongDual 𝕜 E) ↦
      BidualForm.eval (secondArens B) (WeakDual.toStrongDual x)
        (NormedSpace.inclusionInDoubleDual 𝕜 F y) := by
  change Continuous fun x : WeakDual 𝕜 (StrongDual 𝕜 E) ↦
    x ((transpose B) y)
  exact WeakDual.eval_continuous ((transpose B) y)

/-- Equality of the two Arens extensions is exactly weak compactness of the
associated operator. -/
theorem isWeaklyCompact_iff_firstArens_eq_secondArens
    (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    IsWeaklyCompact B ↔ firstArens B = secondArens B := by
  rw [isWeaklyCompact_iff_bidual_range]
  constructor
  · intro h
    apply BidualForm.ext
    intro x y
    rcases h x with ⟨f, hf⟩
    have hfcand : f = dualMap (transpose B) x := by
      apply ContinuousLinearMap.ext
      intro z
      have hz := congrArg
        (fun q : StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) ↦
          q (NormedSpace.inclusionInDoubleDual 𝕜 F z)) hf
      have hmaps : dualMap B
          (NormedSpace.inclusionInDoubleDual 𝕜 F z) = transpose B z := by
        apply ContinuousLinearMap.ext
        intro w
        rfl
      have hz' : x (dualMap B
          (NormedSpace.inclusionInDoubleDual 𝕜 F z)) = f z := by
        simpa using hz
      rw [hmaps] at hz'
      exact hz'.symm
    have hy := congrArg
      (fun q : StrongDual 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F)) ↦ q y) hf
    simpa [hfcand] using hy
  · intro h x
    refine ⟨dualMap (transpose B) x, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    have hy := congrArg (fun C : BidualForm 𝕜 E F ↦
      BidualForm.eval C x y) h
    simpa using hy

private theorem weakStar_ext
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
      [NormedSpace ℝ G] [IsScalarTower ℝ 𝕜 G]
    (L M : BidualModel 𝕜 G →L[𝕜] 𝕜)
    (hL : Continuous fun z : WeakDual 𝕜 (StrongDual 𝕜 G) ↦
      L (ULift.up (WeakDual.toStrongDual z)))
    (hM : Continuous fun z : WeakDual 𝕜 (StrongDual 𝕜 G) ↦
      M (ULift.up (WeakDual.toStrongDual z)))
    (hcanon : ∀ z : G,
      L (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 G z)) =
      M (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 G z))) : L = M := by
  apply ContinuousLinearMap.ext
  intro omega
  let r : ℝ := ‖omega.down‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  let c : 𝕜 := (r⁻¹ : ℝ)
  have hc : ‖c‖ = r⁻¹ := by simp [c, abs_of_pos hr]
  have hunit : ‖c • omega.down‖ ≤ 1 := by
    calc
      ‖c • omega.down‖ ≤ ‖c‖ * ‖omega.down‖ :=
        ContinuousLinearMap.opNorm_smul_le c omega.down
      _ = r⁻¹ * ‖omega.down‖ := by rw [hc]
      _ = ‖omega.down‖ / r := by rw [div_eq_inv_mul]
      _ ≤ 1 := (div_le_one hr).2 (by dsimp [r]; linarith)
  let omegaW : WeakDual 𝕜 (StrongDual 𝕜 G) :=
    StrongDual.toWeakDual (c • omega.down)
  have homegaW : omegaW ∈ NormedSpace.weakStarClosedBall
      (𝕜 := 𝕜) (X := G) 1 := by
    change dist (c • omega.down) 0 ≤ 1
    calc
      dist (c • omega.down) 0 = ‖c • omega.down‖ :=
        dist_zero_right (c • omega.down)
      _ ≤ 1 := hunit
  have hgold := NormedSpace.closedBall_subset_closure_weakStarCanonicalImage
    (𝕜 := 𝕜) (X := G) homegaW
  have hclosed : IsClosed {z : WeakDual 𝕜 (StrongDual 𝕜 G) |
      L (ULift.up (WeakDual.toStrongDual z)) =
        M (ULift.up (WeakDual.toStrongDual z))} :=
    isClosed_eq hL hM
  have hsubset : NormedSpace.weakStarCanonicalImage
      (𝕜 := 𝕜) (X := G) (Metric.closedBall 0 1) ⊆
      {z : WeakDual 𝕜 (StrongDual 𝕜 G) |
        L (ULift.up (WeakDual.toStrongDual z)) =
          M (ULift.up (WeakDual.toStrongDual z))} := by
    rintro _ ⟨_, ⟨z, _, rfl⟩, rfl⟩
    exact hcanon z
  have hscaled : L (ULift.up (c • omega.down)) =
      M (ULift.up (c • omega.down)) :=
    closure_minimal hsubset hclosed hgold
  have hc_mul : (r : 𝕜) * c = 1 := by simp [c, hr.ne']
  have hrescale : (r : 𝕜) • ULift.up (c • omega.down) = omega := by
    rw [show ULift.up (c • omega.down) = c • omega by
      apply ULift.ext
      rfl]
    rw [smul_smul, hc_mul, one_smul]
  calc
    L omega = (r : 𝕜) • L (ULift.up (c • omega.down)) := by
      rw [← map_smul]
      rw [hrescale]
    _ = (r : 𝕜) • M (ULift.up (c • omega.down)) := by rw [hscaled]
    _ = M omega := by
      rw [← map_smul]
      rw [hrescale]

/-- A separately weak-star continuous extension is unique. -/
theorem extension_unique (B : E →L[𝕜] F →L[𝕜] 𝕜)
    {C : BidualForm 𝕜 E F}
    (hC : SeparatelyWeakStarContinuous C) (hExt : Extends B C) :
    C = firstArens B := by
  have hcanonicalFirst : ∀ x : E,
      C (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 E x)) =
        firstArens B
          (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 E x)) := by
    intro x
    apply weakStar_ext
    · exact hC.2 _
    · exact continuousSecond_firstArens_canonical B x
    · intro y
      exact hExt x y
  apply BidualForm.ext
  intro x y
  have hx : C.flip (ULift.up y) = (firstArens B).flip (ULift.up y) := by
    apply weakStar_ext
    · exact hC.1 y
    · exact continuousFirst_firstArens B y
    · intro z
      exact congrArg (fun L : BidualModel 𝕜 F →L[𝕜] 𝕜 ↦
        L (ULift.up y)) (hcanonicalFirst z)
  exact congrArg (fun L : BidualModel 𝕜 E →L[𝕜] 𝕜 ↦
    L (ULift.up x)) hx

private theorem extension_unique_second (B : E →L[𝕜] F →L[𝕜] 𝕜)
    {C : BidualForm 𝕜 E F}
    (hC : SeparatelyWeakStarContinuous C) (hExt : Extends B C) :
    C = secondArens B := by
  have hcanonicalSecond : ∀ y : F,
      C.flip (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 F y)) =
        (secondArens B).flip
          (ULift.up (NormedSpace.inclusionInDoubleDual 𝕜 F y)) := by
    intro y
    apply weakStar_ext
    · exact hC.1 _
    · exact continuousFirst_secondArens_canonical B y
    · intro x
      exact hExt x y
  apply BidualForm.ext
  intro x y
  have hy : C (ULift.up x) = secondArens B (ULift.up x) := by
    apply weakStar_ext
    · exact hC.2 x
    · exact continuousSecond_secondArens B x
    · intro z
      exact congrArg (fun L : BidualModel 𝕜 E →L[𝕜] 𝕜 ↦
        L (ULift.up x)) (hcanonicalSecond z)
  exact congrArg (fun L : BidualModel 𝕜 F →L[𝕜] 𝕜 ↦
    L (ULift.up y)) hy

/-- Weak compactness, Arens equality, and existence of a separately
weak-star continuous extension are equivalent. The extension is necessarily
the first Arens extension and has exactly the original norm. -/
theorem isWeaklyCompact_iff_exists_extension
    (B : E →L[𝕜] F →L[𝕜] 𝕜) :
    IsWeaklyCompact B ↔
      ∃ C : BidualForm 𝕜 E F,
        SeparatelyWeakStarContinuous C ∧ Extends B C ∧ ‖C‖ = ‖B‖ := by
  constructor
  · intro hB
    have hEq := (isWeaklyCompact_iff_firstArens_eq_secondArens B).mp hB
    refine ⟨firstArens B, ⟨continuousFirst_firstArens B, ?_⟩,
      firstArens_canonical B, norm_firstArens B⟩
    rw [hEq]
    exact continuousSecond_secondArens B
  · rintro ⟨C, hC, hExt, _⟩
    apply (isWeaklyCompact_iff_firstArens_eq_secondArens B).2
    rw [← extension_unique B hC hExt,
      ← extension_unique_second B hC hExt]

end

end MathlibAnnex.BidualBilinear
