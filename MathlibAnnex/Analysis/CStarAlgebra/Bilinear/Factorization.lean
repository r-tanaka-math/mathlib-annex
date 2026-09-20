import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Normed.Group.HomCompletion
import Mathlib.Analysis.Normed.Module.Completion
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Domination
import MathlibAnnex.Analysis.Normed.Operator.WeakCompact

set_option autoImplicit false

open scoped ComplexOrder InnerProductSpace

namespace MathlibAnnex.CStarBilinear

universe uA

noncomputable section

variable {A : Type uA} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- A positive linear map between C-star algebras, bundled as a continuous
linear map using Mathlib's automatic boundedness theorem. -/
def positiveToContinuousLinearMap (p : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ where
  toLinearMap := p.toLinearMap
  cont := map_continuous p

@[simp]
theorem positiveToContinuousLinearMap_apply (p : A →ₚ[ℂ] ℂ) (x : A) :
    positiveToContinuousLinearMap p x = p x :=
  rfl

/-- The algebraic pre-Hilbert space carrying the sum of a left and a right
positive-functional seminorm. -/
def TwoSidedPreGNS (p q : A →ₚ[ℂ] ℂ) := A

instance (p q : A →ₚ[ℂ] ℂ) : AddCommGroup (TwoSidedPreGNS p q) :=
  inferInstanceAs (AddCommGroup A)

instance (p q : A →ₚ[ℂ] ℂ) : Module ℂ (TwoSidedPreGNS p q) :=
  inferInstanceAs (Module ℂ A)

/-- The identity map into the two-sided pre-GNS model. -/
def toTwoSidedPreGNS (p q : A →ₚ[ℂ] ℂ) : A ≃ₗ[ℂ] TwoSidedPreGNS p q :=
  LinearEquiv.refl ℂ _

/-- The identity map out of the two-sided pre-GNS model. -/
def ofTwoSidedPreGNS (p q : A →ₚ[ℂ] ℂ) : TwoSidedPreGNS p q ≃ₗ[ℂ] A :=
  (toTwoSidedPreGNS p q).symm

@[simp]
theorem toTwoSidedPreGNS_ofTwoSidedPreGNS
    (p q : A →ₚ[ℂ] ℂ) (x : TwoSidedPreGNS p q) :
    toTwoSidedPreGNS p q (ofTwoSidedPreGNS p q x) = x :=
  rfl

@[simp]
theorem ofTwoSidedPreGNS_toTwoSidedPreGNS
    (p q : A →ₚ[ℂ] ℂ) (x : A) :
    ofTwoSidedPreGNS p q (toTwoSidedPreGNS p q x) = x :=
  rfl

noncomputable abbrev twoSidedPreInnerProductCore (p q : A →ₚ[ℂ] ℂ) :
    PreInnerProductSpace.Core ℂ (TwoSidedPreGNS p q) where
  inner x y :=
    p (star (ofTwoSidedPreGNS p q x) * ofTwoSidedPreGNS p q y) +
      q (ofTwoSidedPreGNS p q y * star (ofTwoSidedPreGNS p q x))
  conj_inner_symm := by
    intro x y
    simp [← Complex.star_def, ← map_star]
  re_inner_nonneg := by
    intro x
    have hp := RCLike.nonneg_iff.mp
      (p.map_nonneg (star_mul_self_nonneg (ofTwoSidedPreGNS p q x)))
    have hxright :
        0 ≤ ofTwoSidedPreGNS p q x * star (ofTwoSidedPreGNS p q x) := by
      simpa only [star_star] using
        (star_mul_self_nonneg (star (ofTwoSidedPreGNS p q x)))
    have hq := RCLike.nonneg_iff.mp
      (q.map_nonneg hxright)
    simpa only [map_add] using add_nonneg hp.1 hq.1
  add_left := by
    intro x y z
    simp [star_add, add_mul, mul_add]
    ring
  smul_left := by
    intro x y c
    simp [star_smul, smul_mul_assoc, mul_smul_comm]
    ring

noncomputable instance (p q : A →ₚ[ℂ] ℂ) :
    SeminormedAddCommGroup (TwoSidedPreGNS p q) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup
    (c := twoSidedPreInnerProductCore p q)

noncomputable instance (p q : A →ₚ[ℂ] ℂ) :
    InnerProductSpace ℂ (TwoSidedPreGNS p q) :=
  InnerProductSpace.ofCore (twoSidedPreInnerProductCore p q)

@[simp]
theorem twoSidedPreGNS_inner (p q : A →ₚ[ℂ] ℂ)
    (x y : TwoSidedPreGNS p q) :
    inner ℂ x y =
      p (star (ofTwoSidedPreGNS p q x) * ofTwoSidedPreGNS p q y) +
        q (ofTwoSidedPreGNS p q y * star (ofTwoSidedPreGNS p q x)) :=
  rfl

/-- The Hilbert completion of the two-sided positive-functional seminorm. -/
abbrev TwoSidedGNS (p q : A →ₚ[ℂ] ℂ) :=
  UniformSpace.Completion (TwoSidedPreGNS p q)

theorem norm_toTwoSidedPreGNS_sq (p q : A →ₚ[ℂ] ℂ) (x : A) :
    ‖toTwoSidedPreGNS p q x‖ ^ 2 =
      (p (star x * x)).re + (q (x * star x)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

/-- A coarse, explicit bound for the canonical map into the two-sided
pre-GNS space.  No normalization of the positive functionals is required. -/
theorem norm_toTwoSidedPreGNS_le (p q : A →ₚ[ℂ] ℂ) (x : A) :
    ‖toTwoSidedPreGNS p q x‖ ≤
      (‖positiveToContinuousLinearMap p‖ +
          ‖positiveToContinuousLinearMap q‖ + 1) * ‖x‖ := by
  let P : A →L[ℂ] ℂ := positiveToContinuousLinearMap p
  let Q : A →L[ℂ] ℂ := positiveToContinuousLinearMap q
  let M : ℝ := ‖P‖ + ‖Q‖
  have hM : 0 ≤ M := add_nonneg (norm_nonneg P) (norm_nonneg Q)
  have hsq : ‖toTwoSidedPreGNS p q x‖ ^ 2 ≤ M * ‖x‖ ^ 2 := by
    rw [norm_toTwoSidedPreGNS_sq]
    calc
      (p (star x * x)).re + (q (x * star x)).re ≤
          ‖p (star x * x)‖ + ‖q (x * star x)‖ :=
        add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
      _ ≤ ‖P‖ * ‖star x * x‖ + ‖Q‖ * ‖x * star x‖ :=
        add_le_add (P.le_opNorm _) (Q.le_opNorm _)
      _ = M * ‖x‖ ^ 2 := by
        simp only [CStarRing.norm_star_mul_self,
          CStarRing.norm_self_mul_star]
        dsimp [M]
        ring
  have hMcoarse : M ≤ (M + 1) ^ 2 := by
    nlinarith [sq_nonneg M]
  have hsq' : ‖toTwoSidedPreGNS p q x‖ ^ 2 ≤
      ((M + 1) * ‖x‖) ^ 2 := by
    calc
      ‖toTwoSidedPreGNS p q x‖ ^ 2 ≤ M * ‖x‖ ^ 2 := hsq
      _ ≤ (M + 1) ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hMcoarse (sq_nonneg ‖x‖)
      _ = ((M + 1) * ‖x‖) ^ 2 := by ring
  have hMone : 0 ≤ M + 1 := by linarith
  have hmain := (sq_le_sq₀ (norm_nonneg (toTwoSidedPreGNS p q x))
    (mul_nonneg hMone (norm_nonneg x))).mp hsq'
  simpa [P, Q, M, add_assoc] using hmain

/-- The canonical bounded map into the two-sided pre-GNS seminormed space. -/
def toTwoSidedPreGNSL (p q : A →ₚ[ℂ] ℂ) :
    A →L[ℂ] TwoSidedPreGNS p q :=
  (toTwoSidedPreGNS p q).toLinearMap.mkContinuous
    (‖positiveToContinuousLinearMap p‖ +
      ‖positiveToContinuousLinearMap q‖ + 1)
    (norm_toTwoSidedPreGNS_le p q)

@[simp]
theorem toTwoSidedPreGNSL_apply (p q : A →ₚ[ℂ] ℂ) (x : A) :
    toTwoSidedPreGNSL p q x = toTwoSidedPreGNS p q x :=
  rfl

/-- The canonical bounded map from the original C-star algebra into the
Hilbert completion of its two-sided positive-functional seminorm. -/
def toTwoSidedGNS (p q : A →ₚ[ℂ] ℂ) : A →L[ℂ] TwoSidedGNS p q :=
  UniformSpace.Completion.toComplL.comp (toTwoSidedPreGNSL p q)

@[simp]
theorem toTwoSidedGNS_apply (p q : A →ₚ[ℂ] ℂ) (x : A) :
    toTwoSidedGNS p q x = (toTwoSidedPreGNS p q x : TwoSidedGNS p q) :=
  rfl

/-- Extend a continuous linear map from a seminormed space to its completion,
with the codomain kept in place when it is already complete. -/
def completionExtension
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [T0Space F]
    [CompleteSpace F] (f : E →L[ℂ] F) :
    UniformSpace.Completion E →L[ℂ] F :=
  let f₀ : NormedAddGroupHom E F :=
    { toFun := f
      map_add' := f.map_add
      bound' := ⟨‖f‖, f.le_opNorm⟩ }
  let g : NormedAddGroupHom (UniformSpace.Completion E) F := f₀.extension
  { toFun := g
    map_add' := g.map_add'
    map_smul' := by
      intro c x
      induction x using UniformSpace.Completion.induction_on with
      | hp =>
          exact isClosed_eq
            (g.continuous.comp (continuous_const_smul c))
            (g.continuous.const_smul c)
      | ih x =>
          rw [← UniformSpace.Completion.coe_smul]
          simp only [g, NormedAddGroupHom.extension_coe]
          exact f.map_smul c x
    cont := g.continuous }

@[simp]
theorem completionExtension_coe
    {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [T0Space F]
    [CompleteSpace F] (f : E →L[ℂ] F) (x : E) :
    completionExtension f (x : UniformSpace.Completion E) = f x := by
  let f₀ : NormedAddGroupHom E F :=
    { toFun := f
      map_add' := f.map_add
      bound' := ⟨‖f‖, f.le_opNorm⟩ }
  change f₀.extension (x : UniformSpace.Completion E) = f x
  rw [NormedAddGroupHom.extension_coe]
  rfl

section Factorization

universe uD

variable {D : Type uD} [NonUnitalCStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- Quantitative domination by the Hilbert seminorms coming from two positive
functionals on each side. -/
def IsTwoSidedDominated
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (p q : A →ₚ[ℂ] ℂ) (r s : D →ₚ[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ x y, ‖B x y‖ ≤
    C * ‖toTwoSidedPreGNS p q x‖ * ‖toTwoSidedPreGNS r s y‖

private def preFactor
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (p q : A →ₚ[ℂ] ℂ) (r s : D →ₚ[ℂ] ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hB : IsTwoSidedDominated B p q r s C) :
    TwoSidedPreGNS p q →L[ℂ] StrongDual ℂ D :=
  let K : ℝ :=
    ‖positiveToContinuousLinearMap r‖ +
      ‖positiveToContinuousLinearMap s‖ + 1
  LinearMap.mkContinuous
    { toFun := fun x ↦ B (ofTwoSidedPreGNS p q x)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
    (C * K) fun x ↦ by
      change ‖B (ofTwoSidedPreGNS p q x)‖ ≤ (C * K) * ‖x‖
      apply (B (ofTwoSidedPreGNS p q x)).opNorm_le_bound
        (mul_nonneg
          (mul_nonneg hC (by
            dsimp [K]
            positivity))
          (norm_nonneg x))
      intro y
      calc
        ‖B (ofTwoSidedPreGNS p q x) y‖ ≤
            C * ‖x‖ * ‖toTwoSidedPreGNS r s y‖ := by
          have hdom := hB (ofTwoSidedPreGNS p q x) y
          change ‖B (ofTwoSidedPreGNS p q x) y‖ ≤
            C * ‖x‖ * ‖toTwoSidedPreGNS r s y‖ at hdom
          exact hdom
        _ ≤ C * ‖x‖ * (K * ‖y‖) :=
          mul_le_mul_of_nonneg_left (norm_toTwoSidedPreGNS_le r s y)
            (mul_nonneg hC (norm_nonneg x))
        _ = (C * K) * ‖x‖ * ‖y‖ := by ring

/-- Domination by two positive-functional seminorms gives an explicit
factorization of the associated operator through a Hilbert space. -/
theorem exists_hilbert_factorization_of_twoSidedDominated
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (p q : A →ₚ[ℂ] ℂ) (r s : D →ₚ[ℂ] ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hB : IsTwoSidedDominated B p q r s C) :
    ∃ V : TwoSidedGNS p q →L[ℂ] StrongDual ℂ D,
      B = V.comp (toTwoSidedGNS p q) := by
  let V : TwoSidedGNS p q →L[ℂ] StrongDual ℂ D :=
    completionExtension (preFactor B p q r s C hC hB)
  refine ⟨V, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  change B x = V (toTwoSidedGNS p q x)
  simp only [V, toTwoSidedGNS_apply, completionExtension_coe]
  rfl

/-- The actual weak-compactness consequence of positive-functional
Grothendieck domination. -/
theorem isWeaklyCompact_of_twoSidedDominated
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (p q : A →ₚ[ℂ] ℂ) (r s : D →ₚ[ℂ] ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hB : IsTwoSidedDominated B p q r s C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  obtain ⟨V, hV⟩ :=
    exists_hilbert_factorization_of_twoSidedDominated B p q r s C hC hB
  rw [hV]
  exact MathlibAnnex.WeakCompact.isWeaklyCompact_of_factorization
    (toTwoSidedGNS p q) V
    MathlibAnnex.WeakCompact.isReflexive_innerProductSpace

end Factorization

section StrongStar

universe uD

variable {D : Type uD} [NonUnitalCStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

/-- Rebundle a continuous positive functional as the positive linear map used
by the two-sided GNS construction. -/
def positiveFunctional
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ phi.toLinearMap hphi

@[simp]
theorem positiveFunctional_apply
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (x : A) : positiveFunctional phi hphi x = phi x :=
  rfl

private theorem norm_eq_re_of_nonnegative {z : ℂ} (hz : 0 ≤ z) :
    ‖z‖ = z.re := by
  have hz' := RCLike.nonneg_iff.mp hz
  have hreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hz'.2
  calc
    ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hreal
    _ = |z.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = z.re := abs_of_nonneg hz'.1

/-- The two-sided pre-GNS norm is exactly the strong-star gauge when the
functional is positive. -/
theorem norm_toTwoSidedPreGNS_eq_strongStarGauge
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (x : A) :
    ‖toTwoSidedPreGNS (positiveFunctional phi hphi)
        (positiveFunctional phi hphi) x‖ = strongStarGauge phi x := by
  have hleft : 0 ≤ phi (star x * x) :=
    hphi _ (star_mul_self_nonneg x)
  have hright0 : 0 ≤ x * star x := by
    simpa only [star_star] using star_mul_self_nonneg (star x)
  have hright : 0 ≤ phi (x * star x) := hphi _ hright0
  apply (sq_eq_sq₀ (norm_nonneg _)
    (strongStarGauge_nonneg phi x)).mp
  rw [norm_toTwoSidedPreGNS_sq]
  change (phi (star x * x)).re + (phi (x * star x)).re =
    strongStarGauge phi x ^ 2
  rw [show strongStarGauge phi x ^ 2 =
      ‖phi (star x * x)‖ + ‖phi (x * star x)‖ by
    rw [strongStarGauge, Real.sq_sqrt]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [norm_eq_re_of_nonnegative hleft,
    norm_eq_re_of_nonnegative hright]

/-- Positive strong-star domination is sufficient for weak compactness.  This
is the factorization step used after a Grothendieck domination theorem has
constructed the controlling positive functionals. -/
theorem isWeaklyCompact_of_strongStarDominated
    (B : A →L[ℂ] D →L[ℂ] ℂ)
    (phi : A →L[ℂ] ℂ) (psi : D →L[ℂ] ℂ) (C : ℝ)
    (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    (hpsi : ∀ d : D, 0 ≤ d → 0 ≤ psi d)
    (hC : 0 ≤ C) (hB : IsStrongStarDominated B phi psi C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  apply isWeaklyCompact_of_twoSidedDominated B
    (positiveFunctional phi hphi) (positiveFunctional phi hphi)
    (positiveFunctional psi hpsi) (positiveFunctional psi hpsi) C hC
  intro x y
  simpa [norm_toTwoSidedPreGNS_eq_strongStarGauge] using hB x y

end StrongStar

end


end MathlibAnnex.CStarBilinear
