import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MathlibAnnex.Analysis.InnerProductSpace.DenseTransport
import MathlibAnnex.Analysis.InnerProductSpace.UnitaryExtension

/-!
# Exact ambient unitary transport from equal Gram kernels

Equal Gram kernels determine an isometry between the two (possibly
rank-deficient) ranges.  It is extended first inside their finite-dimensional
joint span and then by the identity on the ambient orthogonal complement.
The ambient Hilbert space itself is not assumed finite dimensional.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace LinearMap

universe u v

variable {C : Type u} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The synthesis map of a finite vector family. -/
noncomputable def familySynthesis {n : ℕ} (v : Fin n → H) :
    (Fin n → ℂ) →ₗ[ℂ] H where
  toFun c := ∑ i, c i • v i
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem familySynthesis_apply {n : ℕ} (v : Fin n → H)
    (c : Fin n → ℂ) : familySynthesis v c = ∑ i, c i • v i :=
  rfl

@[simp] theorem familySynthesis_single {n : ℕ} (v : Fin n → H) (i : Fin n) :
    familySynthesis v (Pi.single i 1) = v i := by
  simp [familySynthesis, Pi.single_apply]

theorem inner_familySynthesis_eq {n : ℕ} (v w : Fin n → H)
    (hinner : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (c d : Fin n → ℂ) :
    inner ℂ (familySynthesis v c) (familySynthesis v d) =
      inner ℂ (familySynthesis w c) (familySynthesis w d) := by
  simp only [familySynthesis_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hinner]

/-- Equal Gram kernels of two linear maps with finite-dimensional domain are
implemented by a unitary of the arbitrary ambient Hilbert space.  No rank
equality is assumed separately; it follows at the range level from the Gram
identity. -/
theorem exists_ambient_unitary_of_inner_eq (p q : C →ₗ[ℂ] H)
    (hinner : ∀ x y, inner ℂ (p x) (p y) = inner ℂ (q x) (q y)) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∀ x, U (p x) = q x := by
  let K : Submodule ℂ H := LinearMap.range p ⊔ LinearMap.range q
  let pK : C →ₗ[ℂ] K := p.codRestrict K fun x =>
    show p x ∈ K from
      (show LinearMap.range p ≤ K from le_sup_left) (LinearMap.mem_range_self p x)
  let qK : C →ₗ[ℂ] K := q.codRestrict K fun x =>
    show q x ∈ K from
      (show LinearMap.range q ≤ K from le_sup_right) (LinearMap.mem_range_self q x)
  have hinnerK : ∀ x y, inner ℂ (pK x) (pK y) = inner ℂ (qK x) (qK y) :=
    hinner
  let e : LinearMap.range pK ≃ₗ[ℂ] LinearMap.range qK :=
    rangeEquivOfInnerEq pK qK hinnerK
  have he_norm (x : LinearMap.range pK) : ‖e x‖ = ‖x‖ := by
    obtain ⟨c, hc⟩ := x.prop
    have hx : x = ⟨pK c, LinearMap.mem_range_self pK c⟩ := Subtype.ext hc.symm
    rw [hx]
    have hec := rangeEquivOfInnerEq_apply pK qK hinnerK c
    rw [hec]
    change ‖qK c‖ = ‖pK c‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (qK c),
      norm_eq_sqrt_re_inner (𝕜 := ℂ) (pK c), ← hinnerK]
  let eI : LinearMap.range pK ≃ₗᵢ[ℂ] LinearMap.range qK :=
    { e with norm_map' := he_norm }
  let L : LinearMap.range pK →ₗᵢ[ℂ] K :=
    (LinearMap.range qK).subtypeₗᵢ.comp eI.toLinearIsometry
  letI : FiniteDimensional ℂ K := by
    dsimp only [K]
    infer_instance
  let V : K →ₗᵢ[ℂ] K := L.extend
  have hVsurj : Function.Surjective V :=
    LinearMap.surjective_of_injective (f := V.toLinearMap) V.injective
  let UK : K ≃ₗᵢ[ℂ] K := LinearIsometryEquiv.ofSurjective V hVsurj
  let U : H ≃ₗᵢ[ℂ] H := K.extendUnitary UK
  refine ⟨U, fun x => ?_⟩
  have hpx : p x ∈ K :=
    (show LinearMap.range p ≤ K from le_sup_left) (LinearMap.mem_range_self p x)
  rw [show U (p x) = K.extendUnitary UK (p x) by rfl,
    K.extendUnitary_apply_of_mem UK hpx]
  let sx : LinearMap.range pK := ⟨pK x, LinearMap.mem_range_self pK x⟩
  calc
    ((UK ⟨p x, hpx⟩ : K) : H) = ((V (pK x) : K) : H) := rfl
    _ = ((V sx : K) : H) := rfl
    _ = ((L sx : K) : H) := by
      exact congrArg Subtype.val (LinearIsometry.extend_apply L sx)
    _ = q x := by
      have heqI : eI sx =
          ⟨qK x, LinearMap.mem_range_self qK x⟩ := by
        change e sx = ⟨qK x, LinearMap.mem_range_self qK x⟩
        exact rangeEquivOfInnerEq_apply pK qK hinnerK x
      simpa [L, qK] using congrArg
        (fun z : LinearMap.range qK => (((z : K) : H))) heqI

/-- Finite vector families with exactly equal Gram matrices are transported
by one unitary of the whole ambient inner-product space.  Linear dependence,
zero vectors, and an empty family are all allowed. -/
theorem exists_ambient_unitary_of_gram_eq {n : ℕ} (v w : Fin n → H)
    (hinner : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∀ i, U (v i) = w i := by
  obtain ⟨U, hU⟩ := exists_ambient_unitary_of_inner_eq
    (familySynthesis v) (familySynthesis w)
    (inner_familySynthesis_eq v w hinner)
  refine ⟨U, fun i => ?_⟩
  simpa only [familySynthesis_single] using hU (Pi.single i 1)

/-- The inverse of the same ambient unitary transports the second family
back to the first.  Thus exact Gram transport supplies both directions
without choosing a second unitary. -/
theorem exists_ambient_unitary_pair_of_gram_eq {n : ℕ} (v w : Fin n → H)
    (hinner : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j)) :
    ∃ U : H ≃ₗᵢ[ℂ] H,
      (∀ i, U (v i) = w i) ∧ ∀ i, U.symm (w i) = v i := by
  obtain ⟨U, hU⟩ := exists_ambient_unitary_of_gram_eq v w hinner
  refine ⟨U, hU, fun i => ?_⟩
  rw [← hU i]
  exact U.symm_apply_apply (v i)

/-- If two finite families have equal Gram kernels and their spans are
orthogonal, one ambient unitary can be chosen to swap the displayed families
in both directions.  No claim about its action on the remaining complement,
or about self-adjointness, is made here. -/
theorem exists_ambient_unitary_swap_of_gram_eq_of_orthogonal {n : ℕ}
    (v w : Fin n → H)
    (hinner : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (horth : ∀ i j, inner ℂ (v i) (w j) = 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H,
      (∀ i, U (v i) = w i) ∧ ∀ i, U (w i) = v i := by
  let pv : (Fin n → ℂ) →ₗ[ℂ] H := familySynthesis v
  let pw : (Fin n → ℂ) →ₗ[ℂ] H := familySynthesis w
  let p : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] H := pv.coprod pw
  let q : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] H := pw.coprod pv
  have hsynth (c d : Fin n → ℂ) :
      inner ℂ (pv c) (pv d) = inner ℂ (pw c) (pw d) :=
    inner_familySynthesis_eq v w hinner c d
  have hvw (c d : Fin n → ℂ) : inner ℂ (pv c) (pw d) = 0 := by
    simp only [pv, pw, familySynthesis_apply, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, horth, mul_zero, Finset.sum_const_zero]
  have hwv (c d : Fin n → ℂ) : inner ℂ (pw c) (pv d) = 0 := by
    rw [← inner_conj_symm]
    simp only [hvw d c, map_zero]
  have hpq : ∀ x y, inner ℂ (p x) (p y) = inner ℂ (q x) (q y) := by
    intro x y
    simp only [p, q, LinearMap.coprod_apply, inner_add_left, inner_add_right,
      hsynth, hvw, hwv, add_zero, zero_add]
  obtain ⟨U, hU⟩ := exists_ambient_unitary_of_inner_eq p q hpq
  refine ⟨U, fun i => ?_, fun i => ?_⟩
  · simpa only [p, q, LinearMap.coprod_apply, pv, pw, familySynthesis_single,
      map_zero, add_zero, zero_add] using hU (Pi.single i 1, 0)
  · simpa only [p, q, LinearMap.coprod_apply, pv, pw, familySynthesis_single,
      map_zero, add_zero, zero_add] using hU (0, Pi.single i 1)

/-- In the orthogonal equal-Gram case the swapping unitary may be chosen
involutive on the entire ambient Hilbert space.  This construction works in
the joint range of the two synthesis maps and extends the involution by the
identity, so it does not require either displayed family to be independent. -/
theorem exists_ambient_involutive_unitary_swap_of_gram_eq_of_orthogonal
    {n : ℕ} (v w : Fin n → H)
    (hinner : ∀ i j, inner ℂ (v i) (v j) = inner ℂ (w i) (w j))
    (horth : ∀ i j, inner ℂ (v i) (w j) = 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H,
      (∀ i, U (v i) = w i) ∧ (∀ i, U (w i) = v i) ∧
        ∀ x, U (U x) = x := by
  let pv : (Fin n → ℂ) →ₗ[ℂ] H := familySynthesis v
  let pw : (Fin n → ℂ) →ₗ[ℂ] H := familySynthesis w
  let p : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] H := pv.coprod pw
  let q : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] H := pw.coprod pv
  let K : Submodule ℂ H := LinearMap.range p
  let pK : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] K :=
    p.codRestrict K fun x => LinearMap.mem_range_self p x
  let qK : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] K :=
    q.codRestrict K fun x => by
      refine ⟨(x.2, x.1), ?_⟩
      simp [p, q, pv, pw, add_comm]
  have hsynth (c d : Fin n → ℂ) :
      inner ℂ (pv c) (pv d) = inner ℂ (pw c) (pw d) :=
    inner_familySynthesis_eq v w hinner c d
  have hvw (c d : Fin n → ℂ) : inner ℂ (pv c) (pw d) = 0 := by
    simp only [pv, pw, familySynthesis_apply, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, horth, mul_zero, Finset.sum_const_zero]
  have hwv (c d : Fin n → ℂ) : inner ℂ (pw c) (pv d) = 0 := by
    rw [← inner_conj_symm]
    simp only [hvw d c, map_zero]
  have hpq : ∀ x y, inner ℂ (p x) (p y) = inner ℂ (q x) (q y) := by
    intro x y
    simp only [p, q, LinearMap.coprod_apply, inner_add_left, inner_add_right,
      hsynth, hvw, hwv, add_zero, zero_add]
  have hpKsurj : Function.Surjective pK := by
    intro z
    obtain ⟨x, hx⟩ := z.prop
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  have hqKsurj : Function.Surjective qK := by
    intro z
    obtain ⟨x, hx⟩ := z.prop
    refine ⟨(x.2, x.1), Subtype.ext ?_⟩
    simpa [qK, q, p, pv, pw, add_comm] using hx
  have hpqK : ∀ x y, inner ℂ (pK x) (pK y) = inner ℂ (qK x) (qK y) := hpq
  obtain ⟨UK, hUK, -⟩ := existsUnique_linearIsometryEquiv_of_inner_eq
    pK qK hpKsurj.denseRange hqKsurj.denseRange hpqK
  have hUK2 : ∀ z, UK (UK z) = z := by
    intro z
    obtain ⟨x, rfl⟩ := hpKsurj z
    rw [hUK]
    have hswap : qK x = pK (x.2, x.1) := by
      apply Subtype.ext
      simp [qK, pK, q, p, pv, pw, add_comm]
    rw [hswap, hUK]
    apply Subtype.ext
    simp [qK, pK, q, p, pv, pw, add_comm]
  let U : H ≃ₗᵢ[ℂ] H := K.extendUnitary UK
  refine ⟨U, fun i => ?_, fun i => ?_, fun x => ?_⟩
  · have hvK : v i ∈ K := by
      refine ⟨(Pi.single i 1, 0), ?_⟩
      simp [p, pv, pw]
    rw [show U (v i) = K.extendUnitary UK (v i) by rfl,
      K.extendUnitary_apply_of_mem UK hvK]
    have hvrep : (⟨v i, hvK⟩ : K) = pK (Pi.single i 1, 0) := by
      apply Subtype.ext
      simp [pK, p, pv, pw]
    rw [hvrep, hUK]
    simp [qK, q, pv, pw]
  · have hwK : w i ∈ K := by
      refine ⟨(0, Pi.single i 1), ?_⟩
      simp [p, pv, pw]
    rw [show U (w i) = K.extendUnitary UK (w i) by rfl,
      K.extendUnitary_apply_of_mem UK hwK]
    have hwrep : (⟨w i, hwK⟩ : K) = pK (0, Pi.single i 1) := by
      apply Subtype.ext
      simp [pK, p, pv, pw]
    rw [hwrep, hUK]
    simp [qK, q, pv, pw]
  · exact K.extendUnitary_apply_twice UK hUK2 x

end LinearMap

namespace LinearIsometryEquiv

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The negative spectral projection associated to an involutive unitary. -/
noncomputable def involutionProjection (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ H - (U : H →L[ℂ] H))

@[simp] theorem involutionProjection_apply (U : H ≃ₗᵢ[ℂ] H) (x : H) :
    involutionProjection U x = (2 : ℂ)⁻¹ • (x - U x) := rfl

theorem involutionProjection_idempotent (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, U (U x) = x) (x : H) :
    involutionProjection U (involutionProjection U x) =
      involutionProjection U x := by
  simp only [involutionProjection_apply, map_smul, map_sub, hU]
  module

/-- An involutive unitary is symmetric for the Hilbert inner product. -/
theorem involution_inner (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, U (U x) = x) (x y : H) :
    inner ℂ (U x) y = inner ℂ x (U y) := by
  calc
    inner ℂ (U x) y = inner ℂ (U x) (U (U y)) :=
      congrArg (inner ℂ (U x)) (hU y).symm
    _ = inner ℂ x (U y) := U.inner_map_map x (U y)

theorem involutionProjection_inner (U : H ≃ₗᵢ[ℂ] H)
    (hU : ∀ x, U (U x) = x) (x y : H) :
    inner ℂ (involutionProjection U x) y =
      inner ℂ x (involutionProjection U y) := by
  simp only [involutionProjection_apply, inner_smul_left,
    inner_sub_left, inner_smul_right, inner_sub_right,
    involution_inner U hU]
  congr 1
  change (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹
  rw [map_inv₀]
  congr 1
  exact map_ofNat (starRingEnd ℂ) 2

/-- The negative spectral projection of an involutive unitary is an
orthogonal projection. -/
theorem isStarProjection_involutionProjection [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H) (hU : ∀ x, U (U x) = x) :
    IsStarProjection (involutionProjection U) := by
  constructor
  · change involutionProjection U * involutionProjection U =
      involutionProjection U
    apply ContinuousLinearMap.ext
    intro x
    exact involutionProjection_idempotent U hU x
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (involutionProjection_inner U hU)

theorem range_involutionProjection_le (U : H ≃ₗᵢ[ℂ] H) :
    LinearMap.range (involutionProjection U).toLinearMap ≤
      LinearMap.range (U.toLinearMap - LinearMap.id) := by
  rintro y ⟨x, rfl⟩
  refine ⟨(-(2 : ℂ)⁻¹) • x, ?_⟩
  change U ((-(2 : ℂ)⁻¹) • x) - (-(2 : ℂ)⁻¹) • x =
    (2 : ℂ)⁻¹ • (x - U x)
  rw [map_smul]
  module

theorem finiteDimensional_range_involutionProjection
    (U : H ≃ₗᵢ[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (U.toLinearMap - LinearMap.id))] :
    FiniteDimensional ℂ
      (LinearMap.range (involutionProjection U).toLinearMap) :=
  Submodule.finiteDimensional_of_le (range_involutionProjection_le U)

theorem involutionProjection_sub_sub (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    U.involutionProjection (v - w) - (v - w) =
      (2 : ℂ)⁻¹ • ((w - U v) + (U w - v)) := by
  simp only [involutionProjection_apply, map_sub]
  module

theorem involutionProjection_add (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    U.involutionProjection (v + w) =
      (2 : ℂ)⁻¹ • ((v - U w) + (w - U v)) := by
  simp only [involutionProjection_apply, map_add]
  module

/-- The projection almost fixes a difference when the involution almost
swaps its endpoints. -/
theorem norm_involutionProjection_sub_sub_le
    (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    ‖U.involutionProjection (v - w) - (v - w)‖ ≤
      (‖U v - w‖ + ‖U w - v‖) / 2 := by
  rw [involutionProjection_sub_sub, norm_smul]
  have hs : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [hs]
  calc
    (2 : ℝ)⁻¹ * ‖(w - U v) + (U w - v)‖ ≤
        (2 : ℝ)⁻¹ * (‖w - U v‖ + ‖U w - v‖) := by
      gcongr
      exact norm_add_le _ _
    _ = (‖U v - w‖ + ‖U w - v‖) / 2 := by
      rw [norm_sub_rev]
      ring

/-- The projection almost kills a sum when the involution almost swaps its
endpoints. -/
theorem norm_involutionProjection_add_le
    (U : H ≃ₗᵢ[ℂ] H) (v w : H) :
    ‖U.involutionProjection (v + w)‖ ≤
      (‖U v - w‖ + ‖U w - v‖) / 2 := by
  rw [involutionProjection_add, norm_smul]
  have hs : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
  rw [hs]
  calc
    (2 : ℝ)⁻¹ * ‖(v - U w) + (w - U v)‖ ≤
        (2 : ℝ)⁻¹ * (‖v - U w‖ + ‖w - U v‖) := by
      gcongr
      exact norm_add_le _ _
    _ = (‖U v - w‖ + ‖U w - v‖) / 2 := by
      rw [norm_sub_rev v, norm_sub_rev w]
      ring

end LinearIsometryEquiv
