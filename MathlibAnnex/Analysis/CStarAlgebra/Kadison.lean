import MathlibAnnex.Analysis.CStarAlgebra.FiniteInterpolation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Quantitative finite interpolation

This file continues the norm-controlled part of Kadison transitivity.  The
first construction is the bounded transform used to turn an unbounded
self-adjoint interpolant into a contraction.  Its norm and functoriality are
proved in the C*-algebra itself, so no faithfulness assumption on a
representation is used for the norm estimate.
-/

set_option autoImplicit false

open scoped CStarAlgebra ComplexStarModule Ring
open scoped ENNReal lp

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace

/-- The scalar bounded transform `t ↦ 2t / (1 + t²)`. -/
noncomputable def boundedSelfAdjointScalar (t : ℝ) : ℝ :=
  2 * t / (1 + t ^ 2)

theorem continuous_boundedSelfAdjointScalar : Continuous boundedSelfAdjointScalar := by
  unfold boundedSelfAdjointScalar
  have hnum : Continuous (fun t : ℝ => 2 * t) :=
    continuous_const.mul continuous_id
  have hden : Continuous (fun t : ℝ => 1 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  exact hnum.div₀ hden (fun t => ne_of_gt (by positivity))

theorem abs_boundedSelfAdjointScalar_le_one (t : ℝ) :
    |boundedSelfAdjointScalar t| ≤ 1 := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  rw [boundedSelfAdjointScalar, abs_div, abs_of_pos hden, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [div_le_one hden]
  nlinarith [sq_nonneg (|t| - 1), sq_abs t]

/-- Functional-calculus bounded transform of a self-adjoint element. -/
noncomputable def boundedSelfAdjointTransform {A : Type*} [CStarAlgebra A]
    (a : A) : A :=
  cfc boundedSelfAdjointScalar a

theorem isSelfAdjoint_boundedSelfAdjointTransform
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (boundedSelfAdjointTransform a) := by
  exact IsSelfAdjoint.cfc

theorem norm_boundedSelfAdjointTransform_le_one
    {A : Type*} [CStarAlgebra A] (a : A) :
    ‖boundedSelfAdjointTransform a‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  simpa [Real.norm_eq_abs] using abs_boundedSelfAdjointScalar_le_one t

theorem StarAlgHom.map_boundedSelfAdjointTransform
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : IsSelfAdjoint a) :
    φ (boundedSelfAdjointTransform a) = boundedSelfAdjointTransform (φ a) := by
  exact φ.map_cfc boundedSelfAdjointScalar a
    continuous_boundedSelfAdjointScalar.continuousOn
    (by fun_prop) ha (ha.map φ)

/-- An inverse branch for `boundedSelfAdjointScalar` on the open unit
interval. -/
noncomputable def strictContractionPreimageScalar (t : ℝ) : ℝ :=
  t / (1 + Real.sqrt (1 - t ^ 2))

theorem continuous_strictContractionPreimageScalar :
    Continuous strictContractionPreimageScalar := by
  unfold strictContractionPreimageScalar
  have hnum : Continuous (fun t : ℝ => t) := continuous_id
  have hden : Continuous (fun t : ℝ => 1 + Real.sqrt (1 - t ^ 2)) :=
    continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2)))
  exact hnum.div₀ hden (fun t => ne_of_gt (by positivity))

theorem boundedSelfAdjointScalar_strictContractionPreimageScalar
    {t : ℝ} (ht : |t| < 1) :
    boundedSelfAdjointScalar (strictContractionPreimageScalar t) = t := by
  have ht_sq : t ^ 2 < 1 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hrad : 0 ≤ 1 - t ^ 2 := by linarith
  have hsqrt_sq : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt hrad
  have hden : 1 + Real.sqrt (1 - t ^ 2) ≠ 0 :=
    ne_of_gt (by positivity)
  unfold boundedSelfAdjointScalar strictContractionPreimageScalar
  have hdenominator :
      1 + (t / (1 + Real.sqrt (1 - t ^ 2))) ^ 2 =
        2 / (1 + Real.sqrt (1 - t ^ 2)) := by
    field_simp [hden]
    nlinarith [hsqrt_sq]
  rw [hdenominator]
  field_simp [hden]

/-- CFC preimage used before applying the bounded self-adjoint transform. -/
noncomputable def strictContractionPreimage
    {A : Type*} [CStarAlgebra A] (a : A) : A :=
  cfc strictContractionPreimageScalar a

theorem isSelfAdjoint_strictContractionPreimage
    {A : Type*} [CStarAlgebra A] (a : A) :
    IsSelfAdjoint (strictContractionPreimage a) :=
  IsSelfAdjoint.cfc

theorem boundedSelfAdjointTransform_strictContractionPreimage
    {A : Type*} [CStarAlgebra A] [Nontrivial A] {a : A} (ha : IsSelfAdjoint a)
    (ha_norm : ‖a‖ < 1) :
    boundedSelfAdjointTransform (strictContractionPreimage a) = a := by
  unfold boundedSelfAdjointTransform strictContractionPreimage
  rw [← cfc_comp boundedSelfAdjointScalar strictContractionPreimageScalar a ha
    continuous_boundedSelfAdjointScalar.continuousOn
    continuous_strictContractionPreimageScalar.continuousOn]
  calc
    cfc (boundedSelfAdjointScalar ∘ strictContractionPreimageScalar) a =
        cfc id a := by
      apply cfc_congr
      intro t ht
      apply boundedSelfAdjointScalar_strictContractionPreimageScalar
      simpa [Real.norm_eq_abs] using
        (spectrum.norm_le_norm_of_mem ht).trans_lt ha_norm
    _ = a := cfc_id ℝ a

/-! The two resolvents used in the finite-request approximation argument. -/

noncomputable def lowerSelfAdjointResolvent
    {A : Type*} [CStarAlgebra A] (a : A) : A :=
  cfc (fun z : ℂ => (z - Complex.I)⁻¹) a

noncomputable def upperSelfAdjointResolvent
    {A : Type*} [CStarAlgebra A] (a : A) : A :=
  cfc (fun z : ℂ => (z + Complex.I)⁻¹) a

theorem IsSelfAdjoint.sub_I_ne_zero_of_mem_spectrum
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z ∈ spectrum ℂ a) : z - Complex.I ≠ 0 := by
  intro h
  have hzi : z = Complex.I := sub_eq_zero.mp h
  have hzreal := ha.im_eq_zero_of_mem_spectrum hz
  rw [hzi] at hzreal
  norm_num at hzreal

theorem IsSelfAdjoint.add_I_ne_zero_of_mem_spectrum
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z ∈ spectrum ℂ a) : z + Complex.I ≠ 0 := by
  intro h
  have hzi : z = -Complex.I := eq_neg_of_add_eq_zero_left h
  have hzreal := ha.im_eq_zero_of_mem_spectrum hz
  rw [hzi] at hzreal
  norm_num at hzreal

theorem norm_inv_sub_I_le_one {z : ℂ} (hz : z.im = 0) :
    ‖(z - Complex.I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have him : |(z - Complex.I).im| = 1 := by simp [hz]
  have hnorm : 1 ≤ ‖z - Complex.I‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  exact (inv_le_one₀ (zero_lt_one.trans_le hnorm)).2 hnorm

theorem norm_inv_add_I_le_one {z : ℂ} (hz : z.im = 0) :
    ‖(z + Complex.I)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have him : |(z + Complex.I).im| = 1 := by simp [hz]
  have hnorm : 1 ≤ ‖z + Complex.I‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  exact (inv_le_one₀ (zero_lt_one.trans_le hnorm)).2 hnorm

theorem norm_lowerSelfAdjointResolvent_le_one
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    ‖lowerSelfAdjointResolvent a‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro z hz
  exact norm_inv_sub_I_le_one (ha.im_eq_zero_of_mem_spectrum hz)

theorem norm_upperSelfAdjointResolvent_le_one
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    ‖upperSelfAdjointResolvent a‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro z hz
  exact norm_inv_add_I_le_one (ha.im_eq_zero_of_mem_spectrum hz)

theorem IsSelfAdjoint.continuousOn_inv_sub_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    ContinuousOn (fun z : ℂ => (z - Complex.I)⁻¹) (spectrum ℂ a) :=
  (continuousOn_id.sub continuousOn_const).inv₀
    (fun z hz => ha.sub_I_ne_zero_of_mem_spectrum hz)

theorem IsSelfAdjoint.continuousOn_inv_add_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    ContinuousOn (fun z : ℂ => (z + Complex.I)⁻¹) (spectrum ℂ a) :=
  (continuousOn_id.add continuousOn_const).inv₀
    (fun z hz => ha.add_I_ne_zero_of_mem_spectrum hz)

theorem IsSelfAdjoint.cfc_sub_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun z : ℂ => z - Complex.I) a =
      a - algebraMap ℂ A Complex.I := by
  calc
    cfc (fun z : ℂ => z - Complex.I) a =
        cfc id a - cfc (fun _ : ℂ => Complex.I) a :=
      cfc_sub (a := a) (f := id) (g := fun _ : ℂ => Complex.I)
        continuousOn_id continuousOn_const
    _ = a - algebraMap ℂ A Complex.I := by
      rw [cfc_id ℂ a ha.isStarNormal,
        cfc_const Complex.I a ha.isStarNormal]

theorem IsSelfAdjoint.cfc_add_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun z : ℂ => z + Complex.I) a =
      a + algebraMap ℂ A Complex.I := by
  calc
    cfc (fun z : ℂ => z + Complex.I) a =
        cfc id a + cfc (fun _ : ℂ => Complex.I) a :=
      cfc_add (a := a) (f := id) (g := fun _ : ℂ => Complex.I)
        continuousOn_id continuousOn_const
    _ = a + algebraMap ℂ A Complex.I := by
      rw [cfc_id ℂ a ha.isStarNormal,
        cfc_const Complex.I a ha.isStarNormal]

theorem IsSelfAdjoint.isUnit_sub_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    IsUnit (a - algebraMap ℂ A Complex.I) := by
  have hunit := (isUnit_cfc_iff (fun z : ℂ => z - Complex.I) a
    (continuousOn_id.sub continuousOn_const) ha.isStarNormal).2
      (fun z hz => ha.sub_I_ne_zero_of_mem_spectrum hz)
  rw [ha.cfc_sub_I] at hunit
  exact hunit

theorem IsSelfAdjoint.isUnit_add_I
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    IsUnit (a + algebraMap ℂ A Complex.I) := by
  have hunit := (isUnit_cfc_iff (fun z : ℂ => z + Complex.I) a
    (continuousOn_id.add continuousOn_const) ha.isStarNormal).2
      (fun z hz => ha.add_I_ne_zero_of_mem_spectrum hz)
  rw [ha.cfc_add_I] at hunit
  exact hunit

theorem lowerSelfAdjointResolvent_eq_ringInverse
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    lowerSelfAdjointResolvent a =
      (a - algebraMap ℂ A Complex.I)⁻¹ʳ := by
  unfold lowerSelfAdjointResolvent
  rw [cfc_inv (fun z : ℂ => z - Complex.I) a
    (fun z hz => ha.sub_I_ne_zero_of_mem_spectrum hz)
    (continuousOn_id.sub continuousOn_const) ha.isStarNormal]
  rw [ha.cfc_sub_I]

theorem upperSelfAdjointResolvent_eq_ringInverse
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    upperSelfAdjointResolvent a =
      (a + algebraMap ℂ A Complex.I)⁻¹ʳ := by
  unfold upperSelfAdjointResolvent
  rw [cfc_inv (fun z : ℂ => z + Complex.I) a
    (fun z hz => ha.add_I_ne_zero_of_mem_spectrum hz)
    (continuousOn_id.add continuousOn_const) ha.isStarNormal]
  rw [ha.cfc_add_I]

theorem lowerSelfAdjointResolvent_sub
    {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    lowerSelfAdjointResolvent a - lowerSelfAdjointResolvent b =
      lowerSelfAdjointResolvent a * (b - a) * lowerSelfAdjointResolvent b := by
  rw [lowerSelfAdjointResolvent_eq_ringInverse ha,
    lowerSelfAdjointResolvent_eq_ringInverse hb,
    Ring.inverse_sub_inverse (iff_of_true ha.isUnit_sub_I hb.isUnit_sub_I)]
  congr 2
  noncomm_ring

theorem upperSelfAdjointResolvent_sub
    {A : Type*} [CStarAlgebra A] {a b : A}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    upperSelfAdjointResolvent a - upperSelfAdjointResolvent b =
      upperSelfAdjointResolvent a * (b - a) * upperSelfAdjointResolvent b := by
  rw [upperSelfAdjointResolvent_eq_ringInverse ha,
    upperSelfAdjointResolvent_eq_ringInverse hb,
    Ring.inverse_sub_inverse (iff_of_true ha.isUnit_add_I hb.isUnit_add_I)]
  congr 2
  noncomm_ring

theorem inv_sub_I_add_inv_add_I_eq_boundedSelfAdjointScalar
    {z : ℂ} (hz : z.im = 0) :
    (z - Complex.I)⁻¹ + (z + Complex.I)⁻¹ =
      boundedSelfAdjointScalar z.re := by
  have hz_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa [hz]
  rw [hz_eq]
  have hm : (z.re : ℂ) - Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hp : (z.re : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hr : (1 + (z.re : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + z.re ^ 2))
  unfold boundedSelfAdjointScalar
  push_cast
  field_simp [hm, hp, hr]
  ring_nf
  rw [Complex.I_sq]
  norm_num
  ring

theorem boundedSelfAdjointTransform_eq_resolvents
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    boundedSelfAdjointTransform a =
      lowerSelfAdjointResolvent a + upperSelfAdjointResolvent a := by
  unfold boundedSelfAdjointTransform lowerSelfAdjointResolvent
    upperSelfAdjointResolvent
  rw [cfc_real_eq_complex boundedSelfAdjointScalar ha]
  rw [← cfc_add (a := a)
    (f := fun z : ℂ => (z - Complex.I)⁻¹)
    (g := fun z : ℂ => (z + Complex.I)⁻¹)
    ha.continuousOn_inv_sub_I ha.continuousOn_inv_add_I]
  apply cfc_congr
  intro z hz
  exact (inv_sub_I_add_inv_add_I_eq_boundedSelfAdjointScalar
    (ha.im_eq_zero_of_mem_spectrum hz)).symm

theorem norm_lowerSelfAdjointResolvent_sub_apply_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {S T : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (x : H) :
    ‖(lowerSelfAdjointResolvent S - lowerSelfAdjointResolvent T) x‖ ≤
      ‖(T - S) (lowerSelfAdjointResolvent T x)‖ := by
  rw [lowerSelfAdjointResolvent_sub hS hT]
  calc
    ‖(lowerSelfAdjointResolvent S * (T - S) *
        lowerSelfAdjointResolvent T) x‖ =
        ‖lowerSelfAdjointResolvent S
          ((T - S) (lowerSelfAdjointResolvent T x))‖ := by rfl
    _ ≤ ‖lowerSelfAdjointResolvent S‖ *
        ‖(T - S) (lowerSelfAdjointResolvent T x)‖ :=
      (lowerSelfAdjointResolvent S).le_opNorm _
    _ ≤ 1 * ‖(T - S) (lowerSelfAdjointResolvent T x)‖ :=
      mul_le_mul_of_nonneg_right (norm_lowerSelfAdjointResolvent_le_one hS)
        (norm_nonneg _)
    _ = ‖(T - S) (lowerSelfAdjointResolvent T x)‖ := one_mul _

theorem norm_upperSelfAdjointResolvent_sub_apply_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {S T : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (x : H) :
    ‖(upperSelfAdjointResolvent S - upperSelfAdjointResolvent T) x‖ ≤
      ‖(T - S) (upperSelfAdjointResolvent T x)‖ := by
  rw [upperSelfAdjointResolvent_sub hS hT]
  calc
    ‖(upperSelfAdjointResolvent S * (T - S) *
        upperSelfAdjointResolvent T) x‖ =
        ‖upperSelfAdjointResolvent S
          ((T - S) (upperSelfAdjointResolvent T x))‖ := by rfl
    _ ≤ ‖upperSelfAdjointResolvent S‖ *
        ‖(T - S) (upperSelfAdjointResolvent T x)‖ :=
      (upperSelfAdjointResolvent S).le_opNorm _
    _ ≤ 1 * ‖(T - S) (upperSelfAdjointResolvent T x)‖ :=
      mul_le_mul_of_nonneg_right (norm_upperSelfAdjointResolvent_le_one hS)
        (norm_nonneg _)
    _ = ‖(T - S) (upperSelfAdjointResolvent T x)‖ := one_mul _

theorem norm_boundedSelfAdjointTransform_sub_apply_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {S T : H →L[ℂ] H}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) (x : H) :
    ‖(boundedSelfAdjointTransform S - boundedSelfAdjointTransform T) x‖ ≤
      ‖(T - S) (lowerSelfAdjointResolvent T x)‖ +
        ‖(T - S) (upperSelfAdjointResolvent T x)‖ := by
  rw [boundedSelfAdjointTransform_eq_resolvents hS,
    boundedSelfAdjointTransform_eq_resolvents hT]
  have hrearrange :
      (lowerSelfAdjointResolvent S + upperSelfAdjointResolvent S) -
          (lowerSelfAdjointResolvent T + upperSelfAdjointResolvent T) =
        (lowerSelfAdjointResolvent S - lowerSelfAdjointResolvent T) +
          (upperSelfAdjointResolvent S - upperSelfAdjointResolvent T) := by
    abel
  rw [hrearrange]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_lowerSelfAdjointResolvent_sub_apply_le hS hT x)
    (norm_upperSelfAdjointResolvent_sub_apply_le hS hT x))

set_option maxHeartbeats 800000 in
/-- Quantitative Kadison transitivity on the open operator-norm unit ball.
The algebra element is self-adjoint and remains in the closed unit ball.

The proof applies the unbounded self-adjoint interpolation theorem to the two
resolvent vectors for every requested vector.  The resolvent identity then
controls the bounded transform without requiring operator-norm approximation
of the unbounded interpolant. -/
theorem StarAlgHom.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      refine ⟨0, IsSelfAdjoint.zero A, by simp, ?_⟩
      have hzero (x : HilbertSum (fun _ : I => H)) : x = 0 := by
        apply lp.ext
        funext i
        exact isEmptyElim i
      have htarget :
          atomicRepresentation (fun _ : I => π) 0 (finiteHilbertSum ξ) -
            diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
              (finiteHilbertSum ξ) = 0 := hzero _
      rw [htarget, norm_zero]
      simpa using hε
  | inr hI =>
      letI := hI
      let S : H →L[ℂ] H := strictContractionPreimage T
      have hS : IsSelfAdjoint S := isSelfAdjoint_strictContractionPreimage T
      let δ : ℝ := ε / (2 * (Fintype.card I : ℝ))
      have hcard : 0 < (Fintype.card I : ℝ) := by
        exact_mod_cast Fintype.card_pos
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      let η : Sum I I → H := Sum.elim
        (fun i => lowerSelfAdjointResolvent S (ξ i))
        (fun i => upperSelfAdjointResolvent S (ξ i))
      obtain ⟨b, hbself, hb⟩ :=
        π.exists_selfAdjoint_atomic_apply_sub_norm_lt_of_irreducible hπ η S hS hδ
      let a : A := boundedSelfAdjointTransform b
      have haself : IsSelfAdjoint a :=
        isSelfAdjoint_boundedSelfAdjointTransform hbself
      have hanorm : ‖a‖ ≤ 1 := norm_boundedSelfAdjointTransform_le_one b
      refine ⟨a, haself, hanorm, ?_⟩
      have hπbself : IsSelfAdjoint (π b) := hbself.map π
      have hcoord (k : Sum I I) :
          ‖(S - π b) (η k)‖ < δ := by
        have hle := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (atomicRepresentation (fun _ : Sum I I => π) b (finiteHilbertSum η) -
            diagonal (fun _ : Sum I I => S) ‖S‖ (norm_nonneg S) (fun _ => le_rfl)
              (finiteHilbertSum η)) k
        have hdirect : ‖π b (η k) - S (η k)‖ < δ := hle.trans_lt hb
        simpa [norm_sub_rev] using hdirect
      have hpoint (i : I) :
          ‖(boundedSelfAdjointTransform (π b) -
              boundedSelfAdjointTransform S) (ξ i)‖ < 2 * δ := by
        refine (norm_boundedSelfAdjointTransform_sub_apply_le
          hπbself hS (ξ i)).trans_lt ?_
        have hl := hcoord (Sum.inl i)
        have hu := hcoord (Sum.inr i)
        simpa [η, two_mul] using add_lt_add hl hu
      let v : HilbertSum (fun _ : I => H) :=
        atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
          diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
            (finiteHilbertSum ξ)
      have hpreimage : boundedSelfAdjointTransform S = T := by
        exact boundedSelfAdjointTransform_strictContractionPreimage hT hTnorm
      have hmap : π a = boundedSelfAdjointTransform (π b) := by
        exact π.map_boundedSelfAdjointTransform b hbself
      have hvpoint (i : I) : ‖v i‖ < 2 * δ := by
        simpa [v, a, atomicRepresentation_apply, finiteHilbertSum_apply,
          diagonal_apply, hmap, hpreimage] using hpoint i
      let w : I → HilbertSum (fun _ : I => H) :=
        fun i => lp.single 2 i (v i)
      have hvsum : v = ∑ i : I, w i := by
        apply lp.ext
        funext j
        simp only [lp.coeFn_single, lp.coeFn_sum, Finset.sum_apply,
          Finset.sum_pi_single, w]
        simp
      have htriangle : ‖∑ i : I, w i‖ ≤ ∑ i : I, ‖w i‖ := by
        exact norm_sum_le Finset.univ w
      have hsingle (i : I) : ‖w i‖ = ‖v i‖ := by
        dsimp [w]
        exact lp.norm_single (E := fun _ : I => H) (p := 2)
          (by norm_num : (0 : ℝ≥0∞) < 2) i (v i)
      calc
        ‖v‖ = ‖∑ i : I, w i‖ := congrArg norm hvsum
        _ ≤ ∑ i : I, ‖w i‖ := htriangle
        _ = ∑ i : I, ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsingle i
        _ < ∑ _i : I, 2 * δ :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun i _ => hvpoint i)
        _ = ε := by
          simp [δ]
          field_simp

set_option maxHeartbeats 800000 in
/-- Quantitative self-adjoint Kadison transitivity for contractions.  This is
the closed-unit-ball form: boundary operators are first moved a controlled
distance into the open ball, where the resolvent construction applies. -/
theorem StarAlgHom.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible'
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTnorm : ‖T‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  classical
  let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
  let D : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
  let M : ℝ := ‖D x‖
  let q : ℝ := min (1 / 2 : ℝ) (ε / (2 * (M + 1)))
  have hM : 0 ≤ M := norm_nonneg _
  have hqpos : 0 < q := by
    dsimp [q]
    rw [lt_min_iff]
    constructor <;> positivity
  have hqhalf : q ≤ 1 / 2 := by
    exact min_le_left _ _
  have hqbound : q ≤ ε / (2 * (M + 1)) := by
    exact min_le_right _ _
  let r : ℝ := 1 - q
  have hrpos : 0 < r := by
    dsimp [r]
    linarith
  have hrlt : r < 1 := by
    dsimp [r]
    linarith
  let T' : H →L[ℂ] H := r • T
  have hT'self : IsSelfAdjoint T' := by
    rw [IsSelfAdjoint]
    simp [T', hT.star_eq]
  have hT'norm : ‖T'‖ < 1 := by
    calc
      ‖T'‖ = r * ‖T‖ := by
        simp [T', norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hTnorm hrpos.le
      _ < 1 := by simpa using hrlt
  obtain ⟨a, haself, hanorm, ha⟩ :=
    π.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible
      hπ ξ T' hT'self hT'norm (half_pos hε)
  refine ⟨a, haself, hanorm, ?_⟩
  let D' : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => T') ‖T'‖ (norm_nonneg T') (fun _ => le_rfl)
  have hD'scale : D' x = r • D x := by
    apply lp.ext
    funext i
    simp [D', D, x, T', diagonal_apply, finiteHilbertSum_apply]
  have hqmul : q * M < ε / 2 := by
    have hstrict : q * M < q * (M + 1) := by
      exact mul_lt_mul_of_pos_left (by linarith) hqpos
    have hle : q * (M + 1) ≤ ε / 2 := by
      calc
        q * (M + 1) ≤ (ε / (2 * (M + 1))) * (M + 1) :=
          mul_le_mul_of_nonneg_right hqbound (by linarith)
        _ = ε / 2 := by field_simp
    exact hstrict.trans_le hle
  have hscale : ‖D' x - D x‖ < ε / 2 := by
    rw [hD'scale]
    have hrewrite : r • D x - D x = (-q) • D x := by
      dsimp [r]
      rw [sub_smul, one_smul, neg_smul]
      abel
    rw [hrewrite, norm_smul, Real.norm_eq_abs]
    simpa [abs_of_pos hqpos, M] using hqmul
  let u : HilbertSum (fun _ : I => H) :=
    atomicRepresentation (fun _ : I => π) a x
  have hu : ‖u - D' x‖ < ε / 2 := by
    simpa [u, D', x] using ha
  have hrearrange : u - D x = (u - D' x) + (D' x - D x) := by
    abel
  calc
    ‖u - D x‖ ≤ ‖u - D' x‖ + ‖D' x - D x‖ := by
      rw [hrearrange]
      exact norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hu hscale
    _ = ε := by ring

set_option maxHeartbeats 800000 in
/-- Norm-budget form of quantitative self-adjoint Kadison approximation. -/
theorem StarAlgHom.exists_selfAdjoint_atomic_apply_sub_norm_lt_of_irreducible_norm_le
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  classical
  by_cases hTzero : ‖T‖ = 0
  · have hzero : T = 0 := norm_eq_zero.mp hTzero
    subst T
    refine ⟨0, IsSelfAdjoint.zero A, by simp, ?_⟩
    have hz :
        atomicRepresentation (fun _ : I => π) 0 (finiteHilbertSum ξ) -
          diagonal (fun _ : I => (0 : H →L[ℂ] H))
            ‖(0 : H →L[ℂ] H)‖ (norm_nonneg (0 : H →L[ℂ] H))
            (fun _ => le_rfl) (finiteHilbertSum ξ) = 0 := by
      apply lp.ext
      funext i
      simp
    rw [hz, norm_zero]
    exact hε
  · have hTpos : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hTzero)
    let S : H →L[ℂ] H := ‖T‖⁻¹ • T
    have hSself : IsSelfAdjoint S := by
      change IsSelfAdjoint (‖T‖⁻¹ • T)
      rw [IsSelfAdjoint]
      simp [hT.star_eq]
    have hSnorm : ‖S‖ ≤ 1 := by
      change ‖‖T‖⁻¹ • T‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hTpos)]
      field_simp
      exact le_rfl
    obtain ⟨b, hbself, hbnorm, hb⟩ :=
      π.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible'
        hπ ξ S hSself hSnorm (div_pos hε hTpos)
    let a : A := ‖T‖ • b
    have haself : IsSelfAdjoint a := by
      change IsSelfAdjoint (‖T‖ • b)
      rw [IsSelfAdjoint]
      simp [hbself.star_eq]
    have hanorm : ‖a‖ ≤ ‖T‖ := by
      change ‖‖T‖ • b‖ ≤ ‖T‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hTpos]
      nlinarith [norm_nonneg b]
    refine ⟨a, haself, hanorm, ?_⟩
    let x : HilbertSum (fun _ : I => H) := finiteHilbertSum ξ
    let D : HilbertSum (fun _ : I => H) →L[ℂ]
        HilbertSum (fun _ : I => H) :=
      diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
    let D' : HilbertSum (fun _ : I => H) →L[ℂ]
        HilbertSum (fun _ : I => H) :=
      diagonal (fun _ : I => S) ‖S‖ (norm_nonneg S) (fun _ => le_rfl)
    let y : HilbertSum (fun _ : I => H) :=
      atomicRepresentation (fun _ : I => π) b x - D' x
    have hy : ‖y‖ < ε / ‖T‖ := by
      simpa [y, x, D'] using hb
    have hscale :
        atomicRepresentation (fun _ : I => π) a x - D x = ‖T‖ • y := by
      have hpimap : π (‖T‖ • b) = ‖T‖ • π b :=
        LinearMapClass.map_smul_of_tower π ‖T‖ b
      apply lp.ext
      funext i
      simp only [atomicRepresentation_apply, lp.coeFn_sub, Pi.sub_apply,
        D, D', diagonal_apply, y, x, finiteHilbertSum_apply]
      change (π (‖T‖ • b)) (ξ i) - T (ξ i) =
        ‖T‖ • ((π b) (ξ i) - (‖T‖⁻¹ • T) (ξ i))
      rw [hpimap]
      simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_smul]
      rw [mul_inv_cancel₀ hTzero, one_smul]
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos hTpos]
    calc
      ‖T‖ * ‖y‖ < ‖T‖ * (ε / ‖T‖) := mul_lt_mul_of_pos_left hy hTpos
      _ = ε := by field_simp

set_option maxHeartbeats 800000 in
/-- Corner-supported quantitative interpolation.  Compressing the algebra
witness preserves its norm and, on vectors fixed by the represented corner,
only applies the contractive corner projection to the original error. -/
theorem StarAlgHom.exists_cornerSupported_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt
    {A H : Type*} [CStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {e : A} (he : IsStarProjection e)
    {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (hξ : ∀ i, π e (ξ i) = ξ i)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : ‖T‖ ≤ 1)
    (hTrange : (π e) * T = T) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ e * a = a ∧ a * e = a ∧
      ‖atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  classical
  obtain ⟨b, hbself, hbnorm, hb⟩ :=
    π.exists_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt_of_irreducible'
      hπ ξ T hT hTnorm hε
  let a : A := e * b * e
  have haself : IsSelfAdjoint a := by
    rw [IsSelfAdjoint]
    simp only [a, star_mul, he.isSelfAdjoint.star_eq, hbself.star_eq]
    exact (mul_assoc e b e).symm
  have hanorm : ‖a‖ ≤ 1 := by
    calc
      ‖a‖ ≤ ‖e‖ * ‖b‖ * ‖e‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * 1 * 1 := by gcongr <;> exact he.norm_le
      _ = 1 := by ring
  have haleft : e * a = a := by
    dsimp [a]
    calc
      e * (e * b * e) = (e * e) * b * e := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  have haright : a * e = a := by
    dsimp [a]
    calc
      e * b * e * e = e * b * (e * e) := by noncomm_ring
      _ = e * b * e := by rw [he.isIdempotentElem.eq]
  refine ⟨a, haself, hanorm, haleft, haright, ?_⟩
  let P : H →L[ℂ] H := π e
  have hP : IsStarProjection P := he.map π
  let Q : HilbertSum (fun _ : I => H) →L[ℂ]
      HilbertSum (fun _ : I => H) :=
    diagonal (fun _ : I => P) 1 zero_le_one (fun _ => hP.norm_le)
  let raw : HilbertSum (fun _ : I => H) :=
    atomicRepresentation (fun _ : I => π) b (finiteHilbertSum ξ) -
      diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
        (finiteHilbertSum ξ)
  let out : HilbertSum (fun _ : I => H) :=
    atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
      diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
        (finiteHilbertSum ξ)
  have hout : out = Q raw := by
    apply lp.ext
    funext i
    simp only [out, raw, Q, P, atomicRepresentation_apply,
      finiteHilbertSum_apply, lp.coeFn_sub, Pi.sub_apply, diagonal_apply]
    have hmap : π a = (π e) * (π b) * (π e) := by simp [a]
    rw [hmap]
    change π e (π b (π e (ξ i))) - T (ξ i) =
      π e (π b (ξ i) - T (ξ i))
    rw [hξ i, map_sub]
    have hTout : π e (T (ξ i)) = T (ξ i) := by
      have happ := congrArg (fun S : H →L[ℂ] H => S (ξ i)) hTrange
      exact happ
    rw [hTout]
  rw [show
    atomicRepresentation (fun _ : I => π) a (finiteHilbertSum ξ) -
      diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
        (finiteHilbertSum ξ) = out by rfl, hout]
  calc
    ‖Q raw‖ ≤ ‖Q‖ * ‖raw‖ := Q.le_opNorm raw
    _ ≤ 1 * ‖raw‖ := by
      gcongr
      exact norm_diagonal_le (fun _ : I => P) 1 zero_le_one
        (fun _ => hP.norm_le)
    _ < ε := by simpa [raw] using hb
