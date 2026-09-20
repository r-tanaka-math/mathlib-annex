import MathlibAnnex.Analysis.CStarAlgebra.ExactInterpolation

/-!
# Projection normalization identities

Algebraic identities underlying near-identity bilateral normalization on a
finite-dimensional Hilbert subspace.  The inverse is taken in the ambient
operator algebra, not in the finite compression.
-/

set_option autoImplicit false

open scoped ComplexStarModule

namespace MathlibAnnex.Analysis.CStarAlgebra

section Algebra

variable {B : Type*} [Ring B]

/-- The full-space inverse of the block compression gives a one-sided exact
correction without requiring the compression to be invertible as an operator
on the entire Hilbert space. -/
theorem projection_normalizer_mul
    (P T J : B) (hP : P * P = P)
    (hPJ : P * J = J * P)
    (hJ : J * (1 - P * (1 - T) * P) = 1) :
    (1 + (1 - T) * P * J) * T * P = P := by
  have hkey : J * P * T * P = P := by
    have h := congrArg (fun x : B => x * P) hJ
    simp only [one_mul] at h
    calc
      J * P * T * P = (J * (1 - P * (1 - T) * P)) * P := by
        noncomm_ring [hP]
      _ = P := h
  calc
    (1 + (1 - T) * P * J) * T * P =
        T * P + (1 - T) * (J * P * T * P) := by
          noncomm_ring [hPJ]
    _ = P := by rw [hkey]; noncomm_ring

/-- The inverse fixes the orthogonal complement of the compressed projection. -/
theorem projection_inverse_complement
    (P T J : B) (hP : P * P = P)
    (hJ : J * (1 - P * (1 - T) * P) = 1) :
    J * (1 - P) = 1 - P := by
  calc
    J * (1 - P) = (J * (1 - P * (1 - T) * P)) * (1 - P) := by
      noncomm_ring [hP]
    _ = 1 - P := by rw [hJ]; simp

end Algebra

section StarAlgebra

variable {B : Type*} [Ring B] [StarRing B]

/-- The adjoint correction sends the prescribed projection into the inverse
compression. -/
theorem projection_normalizer_star_mul
    (P T J : B) (hP : P * P = P)
    (hPself : IsSelfAdjoint P) (hTself : IsSelfAdjoint T)
    (hJself : IsSelfAdjoint J)
    (hJ : J * (1 - P * (1 - T) * P) = 1) :
    star (1 + (1 - T) * P * J) * P = J * P := by
  have hcomplement := projection_inverse_complement P T J hP hJ
  have hJT : J * P * T * P = P := by
    calc
      J * P * T * P = (J * (1 - P * (1 - T) * P)) * P := by
        noncomm_ring [hP]
      _ = P := by rw [hJ]; simp
  calc
    star (1 + (1 - T) * P * J) * P =
        (1 + J * P * (1 - T)) * P := by
          simp only [star_add, star_mul, star_one, star_sub,
            hPself.star_eq, hTself.star_eq, hJself.star_eq]
          noncomm_ring
    _ = P + J * P - J * P * T * P := by noncomm_ring [hP]
    _ = J * P := by rw [hJT]; noncomm_ring

/-- The bilateral correction has the inverse compression as its exact
reducing action on the requested projection. -/
theorem projection_normalizer_conjugate_mul
    (P T J : B) (hP : P * P = P)
    (hPself : IsSelfAdjoint P) (hTself : IsSelfAdjoint T)
    (hJself : IsSelfAdjoint J) (hPJ : P * J = J * P)
    (hJ : J * (1 - P * (1 - T) * P) = 1) :
    (1 + (1 - T) * P * J) * T *
      star (1 + (1 - T) * P * J) * P = J * P := by
  have hleft := projection_normalizer_mul P T J hP hPJ hJ
  have hright := projection_normalizer_star_mul P T J hP hPself hTself hJself hJ
  calc
    (1 + (1 - T) * P * J) * T *
        star (1 + (1 - T) * P * J) * P =
          ((1 + (1 - T) * P * J) * T) *
            (star (1 + (1 - T) * P * J) * P) := by noncomm_ring
    _ = ((1 + (1 - T) * P * J) * T) * (J * P) := by rw [hright]
    _ = ((1 + (1 - T) * P * J) * T * P) * J := by
      rw [← hPJ]
      noncomm_ring
    _ = J * P := by rw [hleft, hPJ]

end StarAlgebra

section Inverse

variable {B : Type*} [CStarAlgebra B]

/-- Ambient inverse of a near-identity compressed operator. -/
noncomputable def compressionInverse (P T : B)
    (h : ‖P * (1 - T) * P‖ < 1) : B :=
  (↑(Units.oneSub (P * (1 - T) * P) h)⁻¹ : B)

theorem compressionInverse_mul (P T : B)
    (h : ‖P * (1 - T) * P‖ < 1) :
    compressionInverse P T h * (1 - P * (1 - T) * P) = 1 := by
  change (↑(Units.oneSub (P * (1 - T) * P) h)⁻¹ : B) *
    (↑(Units.oneSub (P * (1 - T) * P) h) : B) = 1
  exact Units.inv_mul _

theorem mul_compressionInverse (P T : B)
    (h : ‖P * (1 - T) * P‖ < 1) :
    (1 - P * (1 - T) * P) * compressionInverse P T h = 1 := by
  change (↑(Units.oneSub (P * (1 - T) * P) h) : B) *
    (↑(Units.oneSub (P * (1 - T) * P) h)⁻¹ : B) = 1
  exact Units.mul_inv _

theorem compressionInverse_commute_projection (P T : B)
    (hP : P * P = P) (h : ‖P * (1 - T) * P‖ < 1) :
    P * compressionInverse P T h = compressionInverse P T h * P := by
  let J := compressionInverse P T h
  let Z := 1 - P * (1 - T) * P
  have hJZ : J * Z = 1 := compressionInverse_mul P T h
  have hZJ : Z * J = 1 := mul_compressionInverse P T h
  have hPZ : P * Z = Z * P := by
    dsimp [Z]
    noncomm_ring [hP]
    rw [← mul_assoc, hP]
  calc
    P * J = (J * Z) * P * J := by rw [hJZ]; simp
    _ = J * (Z * P) * J := by noncomm_ring
    _ = J * (P * Z) * J := by rw [hPZ]
    _ = J * P * (Z * J) := by noncomm_ring
    _ = J * P := by rw [hZJ]; simp

theorem isSelfAdjoint_compressionInverse (P T : B)
    (hP : IsSelfAdjoint P) (hT : IsSelfAdjoint T)
    (h : ‖P * (1 - T) * P‖ < 1) :
    IsSelfAdjoint (compressionInverse P T h) := by
  let J := compressionInverse P T h
  let Z := 1 - P * (1 - T) * P
  have hJZ : J * Z = 1 := compressionInverse_mul P T h
  have hZJ : Z * J = 1 := mul_compressionInverse P T h
  have hZself : IsSelfAdjoint Z := by
    rw [IsSelfAdjoint]
    dsimp [Z]
    simp only [star_sub, star_mul, star_one, hP.star_eq, hT.star_eq]
    noncomm_ring
  rw [IsSelfAdjoint]
  have hstar : Z * star J = 1 := by
    have hs := congrArg star hJZ
    simpa [star_mul, hZself.star_eq] using hs
  calc
    star J = (J * Z) * star J := by rw [hJZ]; simp
    _ = J * (Z * star J) := by noncomm_ring
    _ = J := by rw [hstar]; simp

/-- Neumann bound derived directly from the inverse identity, without
rebuilding a geometric-series summation API. -/
theorem norm_compressionInverse_le [Nontrivial B] (P T : B)
    (h : ‖P * (1 - T) * P‖ < 1) :
    ‖compressionInverse P T h‖ ≤
      1 / (1 - ‖P * (1 - T) * P‖) := by
  let V : B := P * (1 - T) * P
  let J : B := compressionInverse P T h
  have hJ : J * (1 - V) = 1 := compressionInverse_mul P T h
  have hJ_eq : J = 1 + J * V := by
    calc
      J = J * (1 - V) + J * V := by noncomm_ring
      _ = 1 + J * V := by rw [hJ]
  have hnorm : ‖J‖ ≤ 1 + ‖J‖ * ‖V‖ := by
    calc
      ‖J‖ = ‖1 + J * V‖ := congrArg norm hJ_eq
      _ ≤ ‖(1 : B)‖ + ‖J * V‖ := norm_add_le _ _
      _ ≤ 1 + ‖J‖ * ‖V‖ := by
        simpa [CStarRing.norm_one] using
          (add_le_add_left (norm_mul_le J V) 1)
  have hden : 0 < 1 - ‖V‖ := sub_pos.mpr h
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The concrete near-identity inverse gives an exact bilateral action, with
no extra global inverse supplied as a hypothesis. -/
theorem compression_normalizer_exact (P T : B)
    (hP : IsStarProjection P) (hT : IsSelfAdjoint T)
    (h : ‖P * (1 - T) * P‖ < 1) :
    (1 + (1 - T) * P * compressionInverse P T h) * T *
      star (1 + (1 - T) * P * compressionInverse P T h) * P =
        compressionInverse P T h * P := by
  exact projection_normalizer_conjugate_mul P T (compressionInverse P T h)
    hP.isIdempotentElem.eq hP.isSelfAdjoint hT
    (isSelfAdjoint_compressionInverse P T hP.isSelfAdjoint hT h)
    (compressionInverse_commute_projection P T hP.isIdempotentElem.eq h)
    (compressionInverse_mul P T h)

theorem norm_compression_normalizer_sub_one_le (P T : B)
    (h : ‖P * (1 - T) * P‖ < 1) :
    ‖(1 + (1 - T) * P * compressionInverse P T h) - 1‖ ≤
      ‖(1 - T) * P‖ * ‖compressionInverse P T h‖ := by
  simpa only [add_sub_cancel_left] using
    (norm_mul_le ((1 - T) * P) (compressionInverse P T h))

theorem norm_compressed_residual_le (P T : B)
    (hP : IsStarProjection P) :
    ‖P * (1 - T) * P‖ ≤ ‖(1 - T) * P‖ := by
  calc
    ‖P * (1 - T) * P‖ = ‖P * ((1 - T) * P)‖ := by rw [mul_assoc]
    _ ≤ ‖P‖ * ‖(1 - T) * P‖ := norm_mul_le _ _
    _ ≤ 1 * ‖(1 - T) * P‖ :=
      mul_le_mul_of_nonneg_right hP.norm_le (norm_nonneg _)
    _ = ‖(1 - T) * P‖ := one_mul _

theorem norm_compression_normalizer_sub_one_le_two_mul
    [Nontrivial B] (P T : B) (hP : IsStarProjection P)
    (hV : ‖P * (1 - T) * P‖ < 1)
    (hη : ‖(1 - T) * P‖ < 1 / 2) :
    ‖(1 + (1 - T) * P * compressionInverse P T hV) - 1‖ ≤
      2 * ‖(1 - T) * P‖ := by
  have hVle : ‖P * (1 - T) * P‖ ≤ ‖(1 - T) * P‖ :=
    norm_compressed_residual_le P T hP
  have hVhalf : ‖P * (1 - T) * P‖ < 1 / 2 := hVle.trans_lt hη
  have hden : 0 < 1 - ‖P * (1 - T) * P‖ := sub_pos.mpr hV
  have hfrac : 1 / (1 - ‖P * (1 - T) * P‖) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hJnorm : ‖compressionInverse P T hV‖ ≤ 2 :=
    (norm_compressionInverse_le P T hV).trans hfrac
  calc
    ‖(1 + (1 - T) * P * compressionInverse P T hV) - 1‖ ≤
        ‖(1 - T) * P‖ * ‖compressionInverse P T hV‖ :=
          norm_compression_normalizer_sub_one_le P T hV
    _ ≤ ‖(1 - T) * P‖ * 2 :=
      mul_le_mul_of_nonneg_left hJnorm (norm_nonneg _)
    _ = 2 * ‖(1 - T) * P‖ := by ring

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- Positivity of the compression inverse is the reason the final CFC cutoff
can turn its prescribed action into the identity. -/
theorem one_le_compressionInverse (P T : B)
    (hP : IsStarProjection P) (hT : T ≤ 1)
    (h : ‖P * (1 - T) * P‖ < 1) :
    1 ≤ compressionInverse P T h := by
  let V : B := P * (1 - T) * P
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    simpa [hP.isSelfAdjoint.star_eq] using
      (star_left_conjugate_nonneg (sub_nonneg.mpr hT) P)
  have hVle : V ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg V hVnonneg).mp h.le
  have hZnonneg : 0 ≤ (1 - V : B) := sub_nonneg.mpr hVle
  have hZle : (1 - V : B) ≤ 1 := sub_le_self 1 hVnonneg
  have hzu : (↑(Units.oneSub V h) : B) ≤ 1 := by
    change 1 - V ≤ 1
    exact hZle
  exact (CStarAlgebra.one_le_inv_iff_le_one
    (a := Units.oneSub V h) (by simpa using hZnonneg)).mpr hzu

end Ordered

end Inverse

section Interpolation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- Simultaneous interpolation of an operator and its adjoint on one finite
subspace.  The same algebra element is assembled from sharp self-adjoint
interpolants of the real and imaginary parts. -/
theorem exists_norm_le_two_mul_and_eq_on_with_star
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (T : H →L[ℂ] H) :
    ∃ a : A, ‖a‖ ≤ 2 * ‖T‖ ∧
      (∀ x : H, x ∈ E → pi a x = T x) ∧
      (∀ x : H, x ∈ E → pi (star a) x = star T x) := by
  obtain ⟨h, hh, hhnorm, hhexact⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on pi hpi E
      (ℜ T : H →L[ℂ] H) (ℜ T).prop
  obtain ⟨k, hk, hknorm, hkexact⟩ :=
    exists_selfAdjoint_norm_le_and_eq_on pi hpi E
      (ℑ T : H →L[ℂ] H) (ℑ T).prop
  let a : A := h + Complex.I • k
  have hastar : star a = h - Complex.I • k := by
    dsimp [a]
    simp [star_add, star_smul, hh.star_eq, hk.star_eq, sub_eq_add_neg]
  have hTstar : star T = (ℜ T : H →L[ℂ] H) - Complex.I • (ℑ T : H →L[ℂ] H) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T]
    simp [star_add, star_smul, (ℜ T).prop.star_eq, (ℑ T).prop.star_eq,
      sub_eq_add_neg]
  refine ⟨a, ?_, ?_, ?_⟩
  · calc
      ‖a‖ ≤ ‖h‖ + ‖Complex.I • k‖ := norm_add_le _ _
      _ = ‖h‖ + ‖k‖ := by simp [norm_smul]
      _ ≤ ‖(ℜ T : H →L[ℂ] H)‖ + ‖(ℑ T : H →L[ℂ] H)‖ :=
        add_le_add hhnorm hknorm
      _ ≤ 2 * ‖T‖ := by
        have hr := realPart.norm_le T
        have hi := imaginaryPart.norm_le T
        dsimp at hr hi
        linarith
  · intro x hx
    calc
      pi a x = pi h x + Complex.I • pi k x := by simp [a]
      _ = (ℜ T : H →L[ℂ] H) x + Complex.I • (ℑ T : H →L[ℂ] H) x := by
        rw [hhexact x hx, hkexact x hx]
      _ = T x := by rw [← realPart_add_I_smul_imaginaryPart T]; simp
  · intro x hx
    calc
      pi (star a) x = pi h x - Complex.I • pi k x := by simp [hastar]
      _ = (ℜ T : H →L[ℂ] H) x - Complex.I • (ℑ T : H →L[ℂ] H) x := by
        rw [hhexact x hx, hkexact x hx]
      _ = star T x := by rw [hTstar]; simp

/-- Near-identity form of simultaneous interpolation.  Both the chosen
element and its adjoint have the prescribed action on the same finite space. -/
theorem exists_near_one_interpolant_with_star
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (R : H →L[ℂ] H) :
    ∃ c : A, ‖c - 1‖ ≤ 2 * ‖R - 1‖ ∧
      (∀ x : H, x ∈ E → pi c x = R x) ∧
      (∀ x : H, x ∈ E → pi (star c) x = star R x) := by
  obtain ⟨d, hd, hdexact, hdstar⟩ :=
    exists_norm_le_two_mul_and_eq_on_with_star pi hpi E (R - 1)
  refine ⟨1 + d, ?_, ?_, ?_⟩
  · simpa using hd
  · intro x hx
    have hdx := hdexact x hx
    simp only [sub_apply, one_apply] at hdx
    simp only [map_add, map_one, add_apply, one_apply]
    rw [hdx]
    abel
  · intro x hx
    have hdx := hdstar x hx
    simp only [star_sub, star_one, sub_apply, one_apply] at hdx
    simp only [star_add, star_one, map_add, map_one, add_apply, one_apply]
    rw [hdx]
    abel

/-- Interpolate an ambient bilateral correction on the finite reducing
enlargement of the requested vectors and their images under `pi a`. -/
theorem exists_near_one_conjugate_eq_on
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (a : A) (R : H →L[ℂ] H)
    (hRstar : ∀ x : H, x ∈ E → star R x ∈ E) :
    ∃ c : A, ‖c - 1‖ ≤ 2 * ‖R - 1‖ ∧
      ∀ x : H, x ∈ E →
        pi (c * a * star c) x = (R * pi a * star R) x := by
  let K := finiteReduction E (pi a)
  obtain ⟨c, hcnorm, hcK, hcstarK⟩ :=
    exists_near_one_interpolant_with_star pi hpi K R
  refine ⟨c, hcnorm, ?_⟩
  intro x hx
  have hxK : x ∈ K := (show E ≤ K from le_sup_left) hx
  have hRstarE : star R x ∈ E := hRstar x hx
  have hTRstarK : pi a (star R x) ∈ K := by
    apply (show E.map (pi a).toLinearMap ≤ K from le_sup_right)
    exact ⟨star R x, hRstarE, rfl⟩
  calc
    pi (c * a * star c) x = pi c (pi a (pi (star c) x)) := by
      simp [map_mul, ContinuousLinearMap.mul_apply]
    _ = pi c (pi a (star R x)) := by rw [hcstarK x hxK]
    _ = R (pi a (star R x)) := hcK _ hTRstarK
    _ = (R * pi a * star R) x := by simp [ContinuousLinearMap.mul_apply]

end Interpolation

section LiftedCompression

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- The full-space inverse can be lifted through one algebra element.  This is
the positive, exactly reducing precursor to the final scalar CFC cutoff. -/
theorem exists_lifted_compression_normalizer
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (a : A) (ha : 0 ≤ a) (hTle : pi a ≤ 1)
    (hV : ‖E.starProjection * (1 - pi a) * E.starProjection‖ < 1) :
    let P : H →L[ℂ] H := E.starProjection
    let J := compressionInverse P (pi a) hV
    let R := 1 + (1 - pi a) * P * J
    ∃ c : A, ‖c - 1‖ ≤ 2 * ‖R - 1‖ ∧
      0 ≤ c * a * star c ∧
      pi (c * a * star c) * P = J * P ∧
      1 ≤ J := by
  let P : H →L[ℂ] H := E.starProjection
  let T : H →L[ℂ] H := pi a
  let J : H →L[ℂ] H := compressionInverse P T hV
  let R : H →L[ℂ] H := 1 + (1 - T) * P * J
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hTself : IsSelfAdjoint T := (IsSelfAdjoint.of_nonneg ha).map pi
  have hPJ : P * J = J * P :=
    compressionInverse_commute_projection P T hP.isIdempotentElem.eq hV
  have hJself : IsSelfAdjoint J :=
    isSelfAdjoint_compressionInverse P T hP.isSelfAdjoint hTself hV
  have hRstarP : star R * P = J * P :=
    projection_normalizer_star_mul P T J hP.isIdempotentElem.eq
      hP.isSelfAdjoint hTself hJself (compressionInverse_mul P T hV)
  have hRstarE : ∀ x : H, x ∈ E → star R x ∈ E := by
    intro x hx
    have hPx : P x = x := E.starProjection_eq_self_iff.mpr hx
    have hRx : star R x = J x := by
      have h := congrArg (fun S : H →L[ℂ] H => S x) hRstarP
      simpa [ContinuousLinearMap.mul_apply, hPx] using h
    rw [hRx]
    apply E.starProjection_eq_self_iff.mp
    have h := congrArg (fun S : H →L[ℂ] H => S x) hPJ
    simpa [ContinuousLinearMap.mul_apply, hPx] using h
  obtain ⟨c, hcnorm, hcaction⟩ :=
    exists_near_one_conjugate_eq_on pi hpi E a R hRstarE
  have hbilat : R * T * star R * P = J * P :=
    compression_normalizer_exact P T hP hTself hV
  have hdP : pi (c * a * star c) * P = J * P := by
    apply ContinuousLinearMap.ext
    intro x
    have hc := hcaction (P x) (E.starProjection_apply_mem x)
    have hb := congrArg (fun S : H →L[ℂ] H => S x) hbilat
    simpa [ContinuousLinearMap.mul_apply] using hc.trans hb
  refine ⟨c, hcnorm, star_right_conjugate_nonneg ha c, hdP, ?_⟩
  exact one_le_compressionInverse P T hP hTle hV

end LiftedCompression

section Cutoff

/-- Scalar multiplier for the final positive-contraction cutoff. -/
noncomputable def invSqrtClamp (t : ℝ) : ℝ :=
  (Real.sqrt (max 1 t))⁻¹

/-- Positive contraction clipping; it fixes zero and every value in `[0,1]`. -/
def positiveClip (t : ℝ) : ℝ := min (max t 0) 1

theorem continuous_invSqrtClamp : Continuous invSqrtClamp := by
  unfold invSqrtClamp
  have h : Continuous (fun t : ℝ => Real.sqrt (max 1 t)) :=
    Real.continuous_sqrt.comp (continuous_const.max continuous_id)
  exact h.inv₀ (by intro t; positivity)

theorem continuous_positiveClip : Continuous positiveClip := by
  unfold positiveClip
  fun_prop

theorem invSqrtClamp_mul_self (t : ℝ) (ht : 0 ≤ t) :
    invSqrtClamp t * t * invSqrtClamp t = positiveClip t := by
  by_cases ht1 : t ≤ 1
  · have hmax : max 1 t = 1 := max_eq_left ht1
    have hclip : positiveClip t = t := by
      simp [positiveClip, max_eq_left ht, min_eq_left ht1]
    simp [invSqrtClamp, hmax, hclip]
  · have h1t : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h1t
    have hmax : max 1 t = t := max_eq_right h1t
    have hclip : positiveClip t = 1 := by
      simp [positiveClip, max_eq_left ht, min_eq_right h1t]
    have hsqrt : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr htpos
    have hsquare : Real.sqrt t * Real.sqrt t = t := by
      nlinarith [Real.sq_sqrt ht]
    simp only [invSqrtClamp, hmax, hclip]
    field_simp
    nlinarith

/-- The cutoff multiplier remains within `r` of one when the positive
input has norm at most `(1+r)^2`. -/
theorem abs_invSqrtClamp_sub_one_le (t r : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (htop : t ≤ (1 + r) ^ 2) :
    |invSqrtClamp t - 1| ≤ r := by
  let s := Real.sqrt (max 1 t)
  have hmax0 : 0 ≤ max 1 t := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 t)
  have hsnonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = max 1 t := Real.sq_sqrt hmax0
  have hmax1 : 1 ≤ max 1 t := le_max_left 1 t
  have hs1 : 1 ≤ s := by nlinarith
  have hmaxTop : max 1 t ≤ (1 + r) ^ 2 :=
    max_le (by nlinarith [sq_nonneg r]) htop
  have hsTop : s ≤ 1 + r := by nlinarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs1
  have hfinv : invSqrtClamp t = 1 / s := by
    simp [invSqrtClamp, s, one_div]
  have hfnonneg : 0 ≤ invSqrtClamp t := by rw [hfinv]; positivity
  have hfle : invSqrtClamp t ≤ 1 := by
    rw [hfinv]
    exact (div_le_iff₀ hspos).2 (by simpa using hs1)
  have hfs : invSqrtClamp t * s = 1 := by
    rw [hfinv]
    field_simp
  have hmul : invSqrtClamp t * s ≤ invSqrtClamp t * (1 + r) :=
    mul_le_mul_of_nonneg_left hsTop hfnonneg
  have hfr : invSqrtClamp t * r ≤ r := by
    simpa using (mul_le_mul_of_nonneg_right hfle hr)
  rw [abs_of_nonpos (sub_nonpos.mpr hfle)]
  nlinarith

@[simp] theorem positiveClip_zero : positiveClip 0 = 0 := by
  simp [positiveClip]

theorem positiveClip_nonneg (t : ℝ) : 0 ≤ positiveClip t := by
  unfold positiveClip
  exact le_min (le_max_right _ _) zero_le_one

theorem positiveClip_le_one (t : ℝ) : positiveClip t ≤ 1 := by
  unfold positiveClip
  exact min_le_right _ _

theorem positiveClip_eq_one {t : ℝ} (ht : 1 ≤ t) : positiveClip t = 1 := by
  unfold positiveClip
  rw [max_eq_left (by linarith : 0 ≤ t)]
  exact min_eq_right ht

section CFC

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The scalar cutoff identity lifted to CFC on a positive element. -/
theorem invSqrtClamp_conjugate (d : B) (hd : 0 ≤ d) :
    cfc invSqrtClamp d * d * cfc invSqrtClamp d =
      cfc positiveClip d := by
  have hmul : cfc (fun t : ℝ => invSqrtClamp t * t * invSqrtClamp t) d =
      cfc invSqrtClamp d * d * cfc invSqrtClamp d := by
    have hf : ContinuousOn invSqrtClamp (spectrum ℝ d) :=
      invSqrtClamp_continuous.continuousOn
    have hft : ContinuousOn (fun t : ℝ => invSqrtClamp t * t) (spectrum ℝ d) :=
      hf.mul continuousOn_id
    calc
      cfc (fun t : ℝ => invSqrtClamp t * t * invSqrtClamp t) d =
          cfc (fun t : ℝ => invSqrtClamp t * t) d * cfc invSqrtClamp d :=
            cfc_mul _ _ d (hf := hft) (hg := hf)
      _ = (cfc invSqrtClamp d * cfc (fun t : ℝ => t) d) *
            cfc invSqrtClamp d := by
              rw [cfc_mul invSqrtClamp (fun t : ℝ => t) d
                (hf := hf) (hg := continuousOn_id)]
      _ = cfc invSqrtClamp d * d * cfc invSqrtClamp d := by rw [cfc_id' ℝ d]
  rw [← hmul]
  apply cfc_congr
  intro t ht
  exact invSqrtClamp_mul_self t (spectrum_nonneg_of_nonneg hd ht)

theorem norm_invSqrtClamp_cfc_sub_one_le [Nontrivial B]
    (d : B) (hd : 0 ≤ d) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ‖d‖ ≤ (1 + r) ^ 2) :
    ‖cfc invSqrtClamp d - 1‖ ≤ r := by
  calc
    ‖cfc invSqrtClamp d - 1‖ =
        ‖cfc (fun t : ℝ => invSqrtClamp t - 1) d‖ := by
          rw [cfc_sub invSqrtClamp (fun _ : ℝ => (1 : ℝ)) d
            (hf := invSqrtClamp_continuous.continuousOn)
            (hg := continuousOn_const),
            cfc_const_one (R := ℝ) (ha := IsSelfAdjoint.of_nonneg hd)]
    _ ≤ r := by
      apply norm_cfc_le hr
      intro t ht
      have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hd ht
      have htop : t ≤ (1 + r) ^ 2 := by
        have hn : ‖t‖ ≤ ‖d‖ := spectrum.norm_le_norm_of_mem ht
        rw [Real.norm_eq_abs, abs_of_nonneg ht0] at hn
        exact hn.trans hbound
      exact abs_invSqrtClamp_sub_one_le t r hr ht0 htop

theorem positiveClip_nonneg_cfc (d : B) : 0 ≤ cfc positiveClip d :=
  cfc_nonneg (fun t _ => positiveClip_nonneg t)

theorem norm_positiveClip_cfc_le_one (d : B) : ‖cfc positiveClip d‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (positiveClip_nonneg t)]
  exact positiveClip_le_one t

/-- A positive element whose reducing corner is at least the identity becomes
exactly the identity on that corner after the scalar cutoff. -/
theorem positiveClip_eq_one_on_projection
    (d J P : B) (hd : 0 ≤ d) (hJ : 1 ≤ J)
    (hP : IsStarProjection P) (hdP : Commute d P)
    (hJP : Commute J P) (heq : d * P = J * P) :
    cfc positiveClip d * P = P := by
  have hJnonneg : 0 ≤ J := zero_le_one.trans hJ
  have hJclip : cfc positiveClip J = 1 := by
    calc
      cfc positiveClip J = cfc (fun _ : ℝ => (1 : ℝ)) J := by
        apply cfc_congr
        intro t ht
        exact positiveClip_eq_one ((CFC.one_le_iff J).mp hJ t ht)
      _ = 1 := cfc_const_one (R := ℝ) (a := J)
  calc
    cfc positiveClip d * P = cfc positiveClip J * P :=
      cfc_mul_eq_of_mul_eq (IsSelfAdjoint.of_nonneg hd)
        (IsSelfAdjoint.of_nonneg hJnonneg) hP hdP hJP heq
        positiveClip continuous_positiveClip positiveClip_zero
    _ = P := by rw [hJclip]; simp

/-- The cutoff is realized by a single left multiplier of the original
positive element; it is not merely an additive correction. -/
theorem normalized_conjugate_eq_clip (a c : B) (ha : 0 ≤ a) :
    (cfc invSqrtClamp (c * a * star c) * c) * a *
      star (cfc invSqrtClamp (c * a * star c) * c) =
        cfc positiveClip (c * a * star c) := by
  let d : B := c * a * star c
  have hd : 0 ≤ d := star_right_conjugate_nonneg ha c
  have hfself : IsSelfAdjoint (cfc invSqrtClamp d) := by
    rw [IsSelfAdjoint]
    rw [← cfc_star]
    simp
  calc
    (cfc invSqrtClamp d * c) * a * star (cfc invSqrtClamp d * c) =
        cfc invSqrtClamp d * d * cfc invSqrtClamp d := by
          rw [star_mul, hfself.star_eq]
          dsimp [d]
          noncomm_ring
    _ = cfc positiveClip d := invSqrtClamp_conjugate d hd

theorem normalized_conjugate_nonneg (a c : B) (ha : 0 ≤ a) :
    0 ≤ (cfc invSqrtClamp (c * a * star c) * c) * a *
      star (cfc invSqrtClamp (c * a * star c) * c) := by
  rw [normalized_conjugate_eq_clip a c ha]
  exact positiveClip_nonneg_cfc _

theorem norm_normalized_conjugate_le_one (a c : B) (ha : 0 ≤ a) :
    ‖(cfc invSqrtClamp (c * a * star c) * c) * a *
      star (cfc invSqrtClamp (c * a * star c) * c)‖ ≤ 1 := by
  rw [normalized_conjugate_eq_clip a c ha]
  exact norm_positiveClip_cfc_le_one _

/-- The complete bilateral multiplier remains near one.  This quantitative
bound is independent of the represented Hilbert dimension. -/
theorem norm_normalized_multiplier_sub_one_le [Nontrivial B]
    (a c : B) (ha : 0 ≤ a) (hanorm : ‖a‖ ≤ 1) :
    ‖cfc invSqrtClamp (c * a * star c) * c - 1‖ ≤
      ‖c - 1‖ * (2 + ‖c - 1‖) := by
  let r : ℝ := ‖c - 1‖
  have hr : 0 ≤ r := norm_nonneg _
  have hcnorm : ‖c‖ ≤ 1 + r := by
    have h := norm_add_le (c - 1) (1 : B)
    have heq : (c - 1) + 1 = c := by simp
    rw [heq, CStarRing.norm_one] at h
    linarith
  let d : B := c * a * star c
  have hd : 0 ≤ d := star_right_conjugate_nonneg ha c
  have hdnorm : ‖d‖ ≤ (1 + r) ^ 2 := by
    calc
      ‖d‖ ≤ (‖c‖ * ‖a‖) * ‖star c‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((1 + r) * 1) * (1 + r) := by
        rw [norm_star]
        gcongr
      _ = (1 + r) ^ 2 := by ring
  have hf : ‖cfc invSqrtClamp d - 1‖ ≤ r :=
    norm_invSqrtClamp_cfc_sub_one_le d hd r hr hdnorm
  have hdecomp : cfc invSqrtClamp d * c - 1 =
      (cfc invSqrtClamp d - 1) * c + (c - 1) := by
    noncomm_ring
  rw [hdecomp]
  calc
    ‖(cfc invSqrtClamp d - 1) * c + (c - 1)‖ ≤
        ‖(cfc invSqrtClamp d - 1) * c‖ + ‖c - 1‖ := norm_add_le _ _
    _ ≤ ‖cfc invSqrtClamp d - 1‖ * ‖c‖ + r := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ r * (1 + r) + r := by gcongr
    _ = r * (2 + r) := by ring

theorem map_normalized_conjugate_eq_on_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (pi : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (a c : B) (ha : 0 ≤ a)
    (P J : H →L[ℂ] H) (hP : IsStarProjection P)
    (hJ : 1 ≤ J) (hJP : Commute J P)
    (hdP : pi (c * a * star c) * P = J * P) :
    pi ((cfc invSqrtClamp (c * a * star c) * c) * a *
      star (cfc invSqrtClamp (c * a * star c) * c)) * P = P := by
  let d : B := c * a * star c
  have hd : 0 ≤ d := star_right_conjugate_nonneg ha c
  have hdpi : 0 ≤ pi d := map_nonneg pi hd
  have hJself : IsSelfAdjoint J :=
    IsSelfAdjoint.of_nonneg (zero_le_one.trans hJ)
  have hdcomm : Commute (pi d) P := by
    rw [commute_iff_eq]
    have hstar : star (pi d * P) = star (J * P) := congrArg star hdP
    have hleft : P * pi d = P * J := by
      rw [star_mul, star_mul, hP.isSelfAdjoint.star_eq,
        hJself.star_eq, (IsSelfAdjoint.of_nonneg hdpi).star_eq] at hstar
      exact hstar
    exact hdP.trans (hJP.eq.trans hleft.symm)
  have hmap : pi (cfc positiveClip d) = cfc positiveClip (pi d) :=
    StarAlgHomClass.map_cfc pi positiveClip d
      (hf := positiveClip_continuous.continuousOn)
      (hφ := by fun_prop)
      (ha := IsSelfAdjoint.of_nonneg hd)
      (hφa := IsSelfAdjoint.of_nonneg hdpi)
  rw [normalized_conjugate_eq_clip a c ha, hmap]
  exact positiveClip_eq_one_on_projection (pi d) J P hdpi hJ hP hdcomm hJP hdP

end CFC

end Cutoff

section ExactNormalization

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

/-- Exact bilateral positive-contraction normalization on a finite subspace.
The quantitative near-identity bound is supplied separately. -/
theorem exists_exact_positive_normalizer_on_subspace
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (a : A) (ha : 0 ≤ a) (hTle : pi a ≤ 1)
    (hV : ‖E.starProjection * (1 - pi a) * E.starProjection‖ < 1) :
    ∃ b : A, 0 ≤ b * a * star b ∧ ‖b * a * star b‖ ≤ 1 ∧
      pi (b * a * star b) * E.starProjection = E.starProjection := by
  let P : H →L[ℂ] H := E.starProjection
  let J : H →L[ℂ] H := compressionInverse P (pi a) hV
  obtain ⟨c, _hcnorm, hdnonneg, hdP, hJ⟩ :=
    exists_lifted_compression_normalizer pi hpi E a ha hTle hV
  let b : A := cfc invSqrtClamp (c * a * star c) * c
  refine ⟨b, normalized_conjugate_nonneg a c ha,
    norm_normalized_conjugate_le_one a c ha, ?_⟩
  have hJP : Commute J P := by
    rw [commute_iff_eq]
    exact (compressionInverse_commute_projection P (pi a)
      isStarProjection_starProjection.isIdempotentElem.eq hV).symm
  exact map_normalized_conjugate_eq_on_projection pi a c ha P J
    isStarProjection_starProjection hJ hJP hdP

/-- Quantitative exact normalization from a small finite-rank residual. -/
theorem exists_small_positive_normalizer_on_subspace
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (a : A) (ha : 0 ≤ a) (hanorm : ‖a‖ ≤ 1)
    (hη : ‖(1 - pi a) * E.starProjection‖ < 1 / 4) :
    ∃ b : A,
      ‖b - 1‖ ≤ 12 * ‖(1 - pi a) * E.starProjection‖ ∧
      0 ≤ b * a * star b ∧ ‖b * a * star b‖ ≤ 1 ∧
      pi (b * a * star b) * E.starProjection = E.starProjection := by
  letI : Nontrivial A := nontrivial_of_ne (0 : A) 1 (by
    intro h
    have hh : (0 : H →L[ℂ] H) = 1 := by simpa using congrArg pi h
    exact zero_ne_one hh)
  let P : H →L[ℂ] H := E.starProjection
  let T : H →L[ℂ] H := pi a
  let η : ℝ := ‖(1 - T) * P‖
  have hTnonneg : 0 ≤ T := map_nonneg pi ha
  have hTnorm : ‖T‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le pi.toNonUnitalStarAlgHom a).trans hanorm
  have hTle : T ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg T hTnonneg).mp hTnorm
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hηhalf : η < 1 / 2 := by linarith
  have hV : ‖P * (1 - T) * P‖ < 1 := by
    calc
      ‖P * (1 - T) * P‖ ≤ η := norm_compressed_residual_le P T hP
      _ < 1 / 2 := hηhalf
      _ < 1 := by norm_num
  let J : H →L[ℂ] H := compressionInverse P T hV
  let R : H →L[ℂ] H := 1 + (1 - T) * P * J
  have hRnorm : ‖R - 1‖ ≤ 2 * η :=
    norm_compression_normalizer_sub_one_le_two_mul P T hP hV hηhalf
  obtain ⟨c, hcnorm, hdnonneg, hdP, hJ⟩ :=
    exists_lifted_compression_normalizer pi hpi E a ha hTle hV
  let r : ℝ := ‖c - 1‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrle : r ≤ 4 * η := by nlinarith
  have hr1 : r < 1 := by nlinarith
  let b : A := cfc invSqrtClamp (c * a * star c) * c
  have hbnorm : ‖b - 1‖ ≤ r * (2 + r) :=
    norm_normalized_multiplier_sub_one_le a c ha hanorm
  have hbnorm' : ‖b - 1‖ ≤ 12 * η := by
    have hsq : r * r ≤ r := by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1.le)]
    nlinarith
  have hJP : Commute J P := by
    rw [commute_iff_eq]
    exact (compressionInverse_commute_projection P T
      hP.isIdempotentElem.eq hV).symm
  refine ⟨b, hbnorm', normalized_conjugate_nonneg a c ha,
    norm_normalized_conjugate_le_one a c ha, ?_⟩
  exact map_normalized_conjugate_eq_on_projection pi a c ha P J
    hP hJ hJP hdP

/-- The tolerance is chosen before the positive contraction.  No faithfulness,
separability, or algebraic support for the finite Hilbert projection is used. -/
theorem exists_near_one_positive_normalizer_on_subspace
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (E : Submodule ℂ H) [FiniteDimensional ℂ E]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
        ‖(1 - pi a) * E.starProjection‖ < δ →
        ∃ b : A, ‖b - 1‖ < ε ∧
          0 ≤ b * a * star b ∧ ‖b * a * star b‖ ≤ 1 ∧
          pi (b * a * star b) * E.starProjection = E.starProjection := by
  let δ : ℝ := min (1 / 4) (ε / 24)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro a ha hanorm hη
  have hηq : ‖(1 - pi a) * E.starProjection‖ < 1 / 4 :=
    hη.trans_le (min_le_left _ _)
  obtain ⟨b, hbnorm, hbnonneg, hbcontraction, hbexact⟩ :=
    exists_small_positive_normalizer_on_subspace pi hpi E a ha hanorm hηq
  refine ⟨b, ?_, hbnonneg, hbcontraction, hbexact⟩
  have hδeps : δ ≤ ε / 24 := min_le_right _ _
  nlinarith

/-- Projection form: the finite-rank projection is an arbitrary Hilbert
projection, not assumed to lie in the represented algebra. -/
theorem exists_near_one_positive_normalizer_on_projection
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi)
    (P : H →L[ℂ] H) (hP : IsStarProjection P)
    [FiniteDimensional ℂ P.range]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a : A, 0 ≤ a → ‖a‖ ≤ 1 →
        ‖(1 - pi a) * P‖ < δ →
        ∃ b : A, ‖b - 1‖ < ε ∧
          0 ≤ b * a * star b ∧ ‖b * a * star b‖ ≤ 1 ∧
          pi (b * a * star b) * P = P := by
  obtain ⟨hU, hPU⟩ := isStarProjection_iff_eq_starProjection_range.mp hP
  letI := hU
  obtain ⟨δ, hδ, hresult⟩ :=
    exists_near_one_positive_normalizer_on_subspace pi hpi P.range hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha hanorm happrox
  have happrox' : ‖(1 - pi a) * P.range.starProjection‖ < δ := by
    simpa only [← hPU] using happrox
  obtain ⟨b, hb, hbpos, hbnorm, hbexact⟩ :=
    hresult a ha hanorm happrox'
  have hbexact' : pi (b * a * star b) * P = P := by
    simpa only [← hPU] using hbexact
  exact ⟨b, hb, hbpos, hbnorm, hbexact'⟩

end ExactNormalization

end MathlibAnnex.Analysis.CStarAlgebra
