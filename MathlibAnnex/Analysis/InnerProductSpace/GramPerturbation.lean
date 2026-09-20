import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import MathlibAnnex.Analysis.InnerProductSpace.GramUnitary

/-!
# Uniform Gram perturbation

The first theorem is the compactness step for one fixed finite ambient
Hilbert space.  The final theorem applies it to the joint span of the two
families and takes a minimum over the finitely many possible dimensions.
Thus its `delta` is chosen before the ambient Hilbert space, while rank loss
and zero or repeated vectors remain allowed.
-/

set_option autoImplicit false

open Metric
open scoped InnerProductSpace

namespace MathlibAnnex.InnerProductSpace

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Sum of all entrywise Gram errors for two finite vector families. -/
noncomputable def gramError {n : ℕ} (p : (Fin n → H) × (Fin n → H)) : ℝ :=
  ∑ i, ∑ j, ‖inner ℂ (p.1 i) (p.1 j) - inner ℂ (p.2 i) (p.2 j)‖

theorem gramError_nonneg {n : ℕ} (p : (Fin n → H) × (Fin n → H)) :
    0 ≤ gramError p := by
  unfold gramError
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun j _ => norm_nonneg _

theorem continuous_gramError {n : ℕ} :
    Continuous (gramError : ((Fin n → H) × (Fin n → H)) → ℝ) := by
  unfold gramError
  fun_prop

/-- A pair of finite families can be simultaneously transported to within
`tau` by one ambient unitary. -/
def GramTransportedWithin {n : ℕ} (tau : ℝ)
    (p : (Fin n → H) × (Fin n → H)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] H, ∀ i, ‖U (p.1 i) - p.2 i‖ < tau

theorem isOpen_gramTransportedWithin {n : ℕ} (tau : ℝ) :
    IsOpen {p : (Fin n → H) × (Fin n → H) |
      GramTransportedWithin tau p} := by
  rw [show {p : (Fin n → H) × (Fin n → H) |
      GramTransportedWithin tau p} =
      ⋃ U : H ≃ₗᵢ[ℂ] H, ⋂ i : Fin n,
        {p | ‖U (p.1 i) - p.2 i‖ < tau} by
    ext p
    simp only [Set.mem_setOf_eq, GramTransportedWithin, Set.mem_iUnion,
      Set.mem_iInter]]
  apply isOpen_iUnion
  intro U
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt
  · exact ((U.continuous.comp ((continuous_apply i).comp continuous_fst)).sub
      ((continuous_apply i).comp continuous_snd)).norm
  · exact continuous_const

/-- Approximate transport by a unitary whose square is the identity.  This
is the form needed when the two displayed spans are orthogonal. -/
def GramTransportedWithinInvolution {n : ℕ} (tau : ℝ)
    (p : (Fin n → H) × (Fin n → H)) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] H,
    (∀ i, ‖U (p.1 i) - p.2 i‖ < tau) ∧ ∀ x, U (U x) = x

theorem isOpen_gramTransportedWithinInvolution {n : ℕ} (tau : ℝ) :
    IsOpen {p : (Fin n → H) × (Fin n → H) |
      GramTransportedWithinInvolution tau p} := by
  rw [show {p : (Fin n → H) × (Fin n → H) |
      GramTransportedWithinInvolution tau p} =
      ⋃ U : H ≃ₗᵢ[ℂ] H, ⋃ (_hU : ∀ x, U (U x) = x), ⋂ i : Fin n,
        {p | ‖U (p.1 i) - p.2 i‖ < tau} by
    ext p
    simp only [Set.mem_setOf_eq, GramTransportedWithinInvolution,
      Set.mem_iUnion, Set.mem_iInter]
    constructor
    · rintro ⟨U, hmove, hU⟩
      exact ⟨U, hU, hmove⟩
    · rintro ⟨U, hU, hmove⟩
      exact ⟨U, hmove, hU⟩]
  apply isOpen_iUnion
  intro U
  apply isOpen_iUnion
  intro _hU
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_lt
  · exact ((U.continuous.comp ((continuous_apply i).comp continuous_fst)).sub
      ((continuous_apply i).comp continuous_snd)).norm
  · exact continuous_const

/-- In a fixed finite-dimensional ambient Hilbert space, sufficiently small
total Gram error uniformly gives an approximate ambient unitary.  No rank
stability or linear independence is assumed. -/
theorem exists_delta_gramTransportedWithin
    [FiniteDimensional ℂ H] {n : ℕ} {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (v w : Fin n → H), ‖(v, w)‖ ≤ 1 →
        gramError (v, w) < delta →
          ∃ U : H ≃ₗᵢ[ℂ] H, ∀ i, ‖U (v i) - w i‖ < tau := by
  letI : ProperSpace H := FiniteDimensional.proper ℂ H
  letI : ProperSpace (Fin n → H) := FiniteDimensional.proper ℂ (Fin n → H)
  let K : Set ((Fin n → H) × (Fin n → H)) := closedBall 0 1
  let G : Set ((Fin n → H) × (Fin n → H)) :=
    {p | GramTransportedWithin tau p}
  have hG : IsOpen G := isOpen_gramTransportedWithin tau
  have hbad : IsCompact (K \ G) :=
    (isCompact_closedBall (0 : (Fin n → H) × (Fin n → H)) 1).diff hG
  have hpos : ∀ p ∈ K \ G, 0 < gramError p := by
    intro p hp
    have hnonneg := gramError_nonneg p
    apply lt_of_le_of_ne hnonneg
    intro hzero
    apply hp.2
    have hinner : ∀ i j,
        inner ℂ (p.1 i) (p.1 j) = inner ℂ (p.2 i) (p.2 j) := by
      intro i j
      have houter_all : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          (∑ j, ‖inner ℂ (p.1 i) (p.1 j) -
            inner ℂ (p.2 i) (p.2 j)‖) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)).1
        simpa only [gramError] using hzero.symm
      have houter : (∑ j, ‖inner ℂ (p.1 i) (p.1 j) -
          inner ℂ (p.2 i) (p.2 j)‖) = 0 := by
        exact houter_all i (Finset.mem_univ i)
      have hentry : ‖inner ℂ (p.1 i) (p.1 j) -
          inner ℂ (p.2 i) (p.2 j)‖ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)).1 houter
          j (Finset.mem_univ j)
      exact sub_eq_zero.mp (norm_eq_zero.mp hentry)
    obtain ⟨U, hU⟩ := LinearMap.exists_ambient_unitary_of_gram_eq p.1 p.2 hinner
    exact ⟨U, fun i => by simp only [hU i, sub_self, norm_zero, htau]⟩
  obtain ⟨delta, hdelta, hmin⟩ :=
    hbad.exists_forall_le' continuous_gramError.continuousOn hpos
  refine ⟨delta, hdelta, ?_⟩
  intro v w hvw herr
  by_contra hnot
  have hpbad : (v, w) ∈ K \ G := by
    refine ⟨?_, hnot⟩
    exact mem_closedBall_zero_iff.mpr hvw
  exact (not_lt_of_ge (hmin (v, w) hpbad)) herr

/-- Fixed finite-dimensional compactness step for the orthogonal branch.
The approximating ambient unitary is an involution; no rank equality or
linear independence of either family is assumed. -/
theorem exists_delta_gramTransportedWithinInvolution
    [FiniteDimensional ℂ H] {n : ℕ} {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (v w : Fin n → H), ‖(v, w)‖ ≤ 1 →
        (∀ i j, inner ℂ (v i) (w j) = 0) →
        gramError (v, w) < delta →
          ∃ U : H ≃ₗᵢ[ℂ] H,
            (∀ i, ‖U (v i) - w i‖ < tau) ∧ ∀ x, U (U x) = x := by
  letI : ProperSpace H := FiniteDimensional.proper ℂ H
  letI : ProperSpace (Fin n → H) := FiniteDimensional.proper ℂ (Fin n → H)
  let K : Set ((Fin n → H) × (Fin n → H)) := closedBall 0 1
  let O : Set ((Fin n → H) × (Fin n → H)) :=
    {p | ∀ i j, inner ℂ (p.1 i) (p.2 j) = 0}
  let G : Set ((Fin n → H) × (Fin n → H)) :=
    {p | GramTransportedWithinInvolution tau p}
  have hO : IsClosed O := by
    rw [show O = ⋂ i : Fin n, ⋂ j : Fin n,
        {p : (Fin n → H) × (Fin n → H) |
          inner ℂ (p.1 i) (p.2 j) = 0} by
      ext p
      simp only [O, Set.mem_setOf_eq, Set.mem_iInter]]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_eq
    · fun_prop
    · exact continuous_const
  have hG : IsOpen G := isOpen_gramTransportedWithinInvolution tau
  have hbad : IsCompact ((K ∩ O) \ G) :=
    ((isCompact_closedBall (0 : (Fin n → H) × (Fin n → H)) 1).inter_right hO).diff hG
  have hpos : ∀ p ∈ (K ∩ O) \ G, 0 < gramError p := by
    intro p hp
    have hnonneg := gramError_nonneg p
    apply lt_of_le_of_ne hnonneg
    intro hzero
    apply hp.2
    have hinner : ∀ i j,
        inner ℂ (p.1 i) (p.1 j) = inner ℂ (p.2 i) (p.2 j) := by
      intro i j
      have houter_all : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          (∑ j, ‖inner ℂ (p.1 i) (p.1 j) -
            inner ℂ (p.2 i) (p.2 j)‖) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)).1
        simpa only [gramError] using hzero.symm
      have houter : (∑ j, ‖inner ℂ (p.1 i) (p.1 j) -
          inner ℂ (p.2 i) (p.2 j)‖) = 0 :=
        houter_all i (Finset.mem_univ i)
      have hentry : ‖inner ℂ (p.1 i) (p.1 j) -
          inner ℂ (p.2 i) (p.2 j)‖ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)).1 houter
          j (Finset.mem_univ j)
      exact sub_eq_zero.mp (norm_eq_zero.mp hentry)
    obtain ⟨U, hUv, _hUw, hU2⟩ :=
      LinearMap.exists_ambient_involutive_unitary_swap_of_gram_eq_of_orthogonal
        p.1 p.2 hinner hp.1.2
    exact ⟨U, fun i => by simp only [hUv i, sub_self, norm_zero, htau], hU2⟩
  obtain ⟨delta, hdelta, hmin⟩ :=
    hbad.exists_forall_le' continuous_gramError.continuousOn hpos
  refine ⟨delta, hdelta, ?_⟩
  intro v w hvw horth herr
  by_contra hnot
  have hpbad : (v, w) ∈ (K ∩ O) \ G := by
    refine ⟨⟨?_, horth⟩, hnot⟩
    exact mem_closedBall_zero_iff.mpr hvw
  exact (not_lt_of_ge (hmin (v, w) hpbad)) herr

/-- A dimension-indexed modulus for the fixed finite-dimensional theorem. -/
noncomputable def gramDelta (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1)) : ℝ :=
  Classical.choose (exists_delta_gramTransportedWithin
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)

theorem gramDelta_pos (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1)) : 0 < gramDelta n htau d :=
  (Classical.choose_spec (exists_delta_gramTransportedWithin
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)).1

theorem gramDelta_spec (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1))
    (v w : Fin n → EuclideanSpace ℂ (Fin d.val)) (hvw : ‖(v, w)‖ ≤ 1)
    (herr : gramError (v, w) < gramDelta n htau d) :
    ∃ U : EuclideanSpace ℂ (Fin d.val) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin d.val),
      ∀ i, ‖U (v i) - w i‖ < tau :=
  (Classical.choose_spec (exists_delta_gramTransportedWithin
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)).2 v w hvw herr

/-- A dimension-indexed modulus for the orthogonal involutive theorem. -/
noncomputable def gramInvolutionDelta (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1)) : ℝ :=
  Classical.choose (exists_delta_gramTransportedWithinInvolution
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)

theorem gramInvolutionDelta_pos (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1)) : 0 < gramInvolutionDelta n htau d :=
  (Classical.choose_spec (exists_delta_gramTransportedWithinInvolution
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)).1

theorem gramInvolutionDelta_spec (n : ℕ) {tau : ℝ} (htau : 0 < tau)
    (d : Fin (2 * n + 1))
    (v w : Fin n → EuclideanSpace ℂ (Fin d.val)) (hvw : ‖(v, w)‖ ≤ 1)
    (horth : ∀ i j, inner ℂ (v i) (w j) = 0)
    (herr : gramError (v, w) < gramInvolutionDelta n htau d) :
    ∃ U : EuclideanSpace ℂ (Fin d.val) ≃ₗᵢ[ℂ]
        EuclideanSpace ℂ (Fin d.val),
      (∀ i, ‖U (v i) - w i‖ < tau) ∧ ∀ x, U (U x) = x :=
  (Classical.choose_spec (exists_delta_gramTransportedWithinInvolution
    (H := EuclideanSpace ℂ (Fin d.val)) (n := n) htau)).2
      v w hvw horth herr

/-- The orthogonal Gram-perturbation modulus is uniform over arbitrary
ambient Hilbert spaces.  The resulting ambient unitary is an involution even
when either finite family loses rank. -/
theorem exists_delta_gramTransportedWithinInvolution_uniform
    {n : ℕ} {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (v w : Fin n → E),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, inner ℂ (v i) (w j) = 0) →
        gramError (v, w) < delta →
          ∃ U : E ≃ₗᵢ[ℂ] E,
            (∀ i, ‖U (v i) - w i‖ < tau) ∧
            (∀ x, U (U x) = x) ∧
            FiniteDimensional ℂ
              (LinearMap.range (U.toLinearMap - LinearMap.id)) := by
  classical
  let S : Finset ℝ := Finset.univ.image (gramInvolutionDelta n htau)
  have hS : S.Nonempty := by
    refine ⟨gramInvolutionDelta n htau ⟨0, by omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  let delta : ℝ := S.min' hS
  have hdelta : 0 < delta := by
    have hmem : delta ∈ S := Finset.min'_mem S hS
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hmem
    rw [← hd]
    exact gramInvolutionDelta_pos n htau d
  refine ⟨delta, hdelta, ?_⟩
  intro E _ _ v w hv hw horth herr
  let p : (Fin n → ℂ) →ₗ[ℂ] E := LinearMap.familySynthesis v
  let q : (Fin n → ℂ) →ₗ[ℂ] E := LinearMap.familySynthesis w
  let K : Submodule ℂ E := LinearMap.range p ⊔ LinearMap.range q
  let vK : Fin n → K := fun i =>
    ⟨v i, (show LinearMap.range p ≤ K from le_sup_left)
      (show v i ∈ LinearMap.range p by
        refine ⟨Pi.single i 1, ?_⟩
        exact LinearMap.familySynthesis_single v i)⟩
  let wK : Fin n → K := fun i =>
    ⟨w i, (show LinearMap.range q ≤ K from le_sup_right)
      (show w i ∈ LinearMap.range q by
        refine ⟨Pi.single i 1, ?_⟩
        exact LinearMap.familySynthesis_single w i)⟩
  letI : FiniteDimensional ℂ K := by
    dsimp only [K]
    infer_instance
  have hdim : Module.finrank ℂ K ≤ 2 * n := by
    calc
      Module.finrank ℂ K ≤
          Module.finrank ℂ (LinearMap.range p) +
            Module.finrank ℂ (LinearMap.range q) := by
        exact Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ n + n := by
        apply Nat.add_le_add
        · simpa only [Module.finrank_fin_fun] using LinearMap.finrank_range_le p
        · simpa only [Module.finrank_fin_fun] using LinearMap.finrank_range_le q
      _ = 2 * n := by omega
  let d : Fin (2 * n + 1) := ⟨Module.finrank ℂ K, by omega⟩
  let e : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d.val) :=
    (stdOrthonormalBasis ℂ K).repr
  let ve : Fin n → EuclideanSpace ℂ (Fin d.val) := fun i => e (vK i)
  let we : Fin n → EuclideanSpace ℂ (Fin d.val) := fun i => e (wK i)
  have hv_one : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have hi : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hw_one : ∀ i, ‖w i‖ ≤ 1 := by
    intro i
    have hi : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (w i)]
  have hpair : ‖(ve, we)‖ ≤ 1 := by
    rw [Prod.norm_def, max_le_iff]
    constructor
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      calc
        ‖ve i‖ = ‖vK i‖ := e.norm_map (vK i)
        _ = ‖v i‖ := rfl
        _ ≤ 1 := hv_one i
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      calc
        ‖we i‖ = ‖wK i‖ := e.norm_map (wK i)
        _ = ‖w i‖ := rfl
        _ ≤ 1 := hw_one i
  have horth_e : ∀ i j, inner ℂ (ve i) (we j) = 0 := by
    intro i j
    rw [show inner ℂ (ve i) (we j) = inner ℂ (vK i) (wK j) by
      exact e.inner_map_map (vK i) (wK j)]
    exact horth i j
  have herr_eq : gramError (ve, we) = gramError (v, w) := by
    unfold gramError
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show inner ℂ (ve i) (ve j) = inner ℂ (vK i) (vK j) by
      exact e.inner_map_map (vK i) (vK j)]
    rw [show inner ℂ (we i) (we j) = inner ℂ (wK i) (wK j) by
      exact e.inner_map_map (wK i) (wK j)]
    rfl
  have hdelta_d : delta ≤ gramInvolutionDelta n htau d := by
    exact Finset.min'_le S (gramInvolutionDelta n htau d)
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
  obtain ⟨U0, hU0, hU02⟩ := gramInvolutionDelta_spec n htau d ve we hpair
    horth_e (by rw [herr_eq]; exact lt_of_lt_of_le herr hdelta_d)
  let UK : K ≃ₗᵢ[ℂ] K := e.trans (U0.trans e.symm)
  have hUK2 : ∀ x, UK (UK x) = x := by
    intro x
    simp only [UK, LinearIsometryEquiv.trans_apply, e.apply_symm_apply]
    rw [hU02, e.symm_apply_apply]
  let U : E ≃ₗᵢ[ℂ] E := K.extendUnitary UK
  refine ⟨U, fun i => ?_, fun x => ?_, ?_⟩
  · have hvi : v i ∈ K := (vK i).prop
    rw [show U (v i) = K.extendUnitary UK (v i) by rfl,
      K.extendUnitary_apply_of_mem UK hvi]
    change ‖UK (vK i) - wK i‖ < tau
    rw [← e.norm_map, map_sub]
    simpa only [UK, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply, ve, we] using hU0 i
  · exact K.extendUnitary_apply_twice UK hUK2 x
  · exact K.finiteDimensional_range_extendUnitary_sub_id UK

/-- Small total Gram error gives a simultaneous approximate ambient unitary,
with one modulus valid for every complex Hilbert space in the universe.

The proof works in the joint span of both families, whose dimension is at
most `2 * n`.  It therefore does not require the two individual spans to
have equal rank. -/
theorem exists_delta_gramTransportedWithin_uniform {n : ℕ} {tau : ℝ}
    (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (v w : Fin n → E),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        gramError (v, w) < delta →
          ∃ U : E ≃ₗᵢ[ℂ] E, ∀ i, ‖U (v i) - w i‖ < tau := by
  classical
  let S : Finset ℝ := Finset.univ.image (gramDelta n htau)
  have hS : S.Nonempty := by
    refine ⟨gramDelta n htau ⟨0, by omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩
  let delta : ℝ := S.min' hS
  have hdelta : 0 < delta := by
    have hmem : delta ∈ S := Finset.min'_mem S hS
    obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hmem
    rw [← hd]
    exact gramDelta_pos n htau d
  refine ⟨delta, hdelta, ?_⟩
  intro E _ _ v w hv hw herr
  let p : (Fin n → ℂ) →ₗ[ℂ] E := LinearMap.familySynthesis v
  let q : (Fin n → ℂ) →ₗ[ℂ] E := LinearMap.familySynthesis w
  let K : Submodule ℂ E := LinearMap.range p ⊔ LinearMap.range q
  let vK : Fin n → K := fun i =>
    ⟨v i, (show LinearMap.range p ≤ K from le_sup_left)
      (show v i ∈ LinearMap.range p by
        refine ⟨Pi.single i 1, ?_⟩
        exact LinearMap.familySynthesis_single v i)⟩
  let wK : Fin n → K := fun i =>
    ⟨w i, (show LinearMap.range q ≤ K from le_sup_right)
      (show w i ∈ LinearMap.range q by
        refine ⟨Pi.single i 1, ?_⟩
        exact LinearMap.familySynthesis_single w i)⟩
  letI : FiniteDimensional ℂ K := by
    dsimp only [K]
    infer_instance
  have hdim : Module.finrank ℂ K ≤ 2 * n := by
    calc
      Module.finrank ℂ K ≤
          Module.finrank ℂ (LinearMap.range p) +
            Module.finrank ℂ (LinearMap.range q) := by
        exact Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ n + n := by
        apply Nat.add_le_add
        · simpa only [Module.finrank_fin_fun] using LinearMap.finrank_range_le p
        · simpa only [Module.finrank_fin_fun] using LinearMap.finrank_range_le q
      _ = 2 * n := by omega
  let d : Fin (2 * n + 1) :=
    ⟨Module.finrank ℂ K, by omega⟩
  let e : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d.val) :=
    (stdOrthonormalBasis ℂ K).repr
  let ve : Fin n → EuclideanSpace ℂ (Fin d.val) := fun i => e (vK i)
  let we : Fin n → EuclideanSpace ℂ (Fin d.val) := fun i => e (wK i)
  have hv_one : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have hi : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i)]
  have hw_one : ∀ i, ‖w i‖ ≤ 1 := by
    intro i
    have hi : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (w i)]
  have hpair : ‖(ve, we)‖ ≤ 1 := by
    rw [Prod.norm_def, max_le_iff]
    constructor
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      calc
        ‖ve i‖ = ‖vK i‖ := e.norm_map (vK i)
        _ = ‖v i‖ := rfl
        _ ≤ 1 := hv_one i
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      calc
        ‖we i‖ = ‖wK i‖ := e.norm_map (wK i)
        _ = ‖w i‖ := rfl
        _ ≤ 1 := hw_one i
  have herr_eq : gramError (ve, we) = gramError (v, w) := by
    unfold gramError
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show inner ℂ (ve i) (ve j) = inner ℂ (vK i) (vK j) by
      exact e.inner_map_map (vK i) (vK j)]
    rw [show inner ℂ (we i) (we j) = inner ℂ (wK i) (wK j) by
      exact e.inner_map_map (wK i) (wK j)]
    rfl
  have hdelta_d : delta ≤ gramDelta n htau d := by
    exact Finset.min'_le S (gramDelta n htau d)
      (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩)
  obtain ⟨U0, hU0⟩ := gramDelta_spec n htau d ve we hpair
    (by rw [herr_eq]; exact lt_of_lt_of_le herr hdelta_d)
  let UK : K ≃ₗᵢ[ℂ] K := e.trans (U0.trans e.symm)
  let U : E ≃ₗᵢ[ℂ] E := K.extendUnitary UK
  refine ⟨U, fun i => ?_⟩
  have hvi : v i ∈ K := (vK i).prop
  rw [show U (v i) = K.extendUnitary UK (v i) by rfl,
    K.extendUnitary_apply_of_mem UK hvi]
  change ‖UK (vK i) - wK i‖ < tau
  rw [← e.norm_map]
  rw [map_sub]
  simpa only [UK, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, ve, we] using hU0 i

/-- Entrywise form of uniform Gram perturbation.  The quantifier order is
`n`, `tau`, `delta`, and only then the ambient Hilbert space and vectors. -/
theorem exists_delta_gramPerturbation {n : ℕ} {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (v w : Fin n → E),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < delta) →
          ∃ U : E ≃ₗᵢ[ℂ] E, ∀ i, ‖U (v i) - w i‖ < tau := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    intro E _ _ v w _ _ _
    refine ⟨LinearIsometryEquiv.refl ℂ E, fun i => ?_⟩
    exact Fin.elim0 i
  · obtain ⟨deltaTotal, hdeltaTotal, htotal⟩ :=
      exists_delta_gramTransportedWithin_uniform (n := n) htau
    let delta : ℝ := deltaTotal / ((n : ℝ) * (n : ℝ))
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hden : 0 < (n : ℝ) * (n : ℝ) := mul_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hdelta : 0 < delta := div_pos hdeltaTotal hden
    refine ⟨delta, hdelta, ?_⟩
    intro E _ _ v w hv hw herr
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    apply htotal v w hv hw
    unfold gramError
    calc
      (∑ i, ∑ j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖) <
          ∑ _i : Fin n, ∑ _j : Fin n, delta := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro i _
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro j _
        exact herr i j
      _ = (n : ℝ) * ((n : ℝ) * delta) := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = deltaTotal := by
        dsimp only [delta]
        field_simp

/-- The same unitary and its actual inverse give the forward and reverse
approximations.  This is not a claim that the unitary is self-adjoint. -/
theorem exists_delta_gramPerturbation_pair {n : ℕ} {tau : ℝ}
    (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (v w : Fin n → E),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < delta) →
          ∃ U : E ≃ₗᵢ[ℂ] E,
            (∀ i, ‖U (v i) - w i‖ < tau) ∧
            ∀ i, ‖U.symm (w i) - v i‖ < tau := by
  obtain ⟨delta, hdelta, hmain⟩ := exists_delta_gramPerturbation (n := n) htau
  refine ⟨delta, hdelta, ?_⟩
  intro E _ _ v w hv hw herr
  obtain ⟨U, hU⟩ := hmain v w hv hw herr
  refine ⟨U, hU, fun i => ?_⟩
  calc
    ‖U.symm (w i) - v i‖ = ‖U (U.symm (w i) - v i)‖ :=
      (U.norm_map (U.symm (w i) - v i)).symm
    _ = ‖w i - U (v i)‖ := by simp
    _ = ‖U (v i) - w i‖ := norm_sub_rev _ _
    _ < tau := hU i

/-- Entrywise orthogonal Gram perturbation.  The same ambient unitary
approximately swaps the two families and is exactly involutive on every
ambient vector.  In particular the conclusion remains valid across rank
loss and for zero or repeated input vectors. -/
theorem exists_delta_orthogonalGramPerturbation {n : ℕ} {tau : ℝ}
    (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (v w : Fin n → E),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, inner ℂ (v i) (w j) = 0) →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < delta) →
          ∃ U : E ≃ₗᵢ[ℂ] E,
            (∀ i, ‖U (v i) - w i‖ < tau) ∧
            (∀ i, ‖U (w i) - v i‖ < tau) ∧
            (∀ x, U (U x) = x) ∧
            FiniteDimensional ℂ
              (LinearMap.range (U.toLinearMap - LinearMap.id)) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    intro E _ _ v w _ _ _ _
    let K : Submodule ℂ E := ⊥
    let U : E ≃ₗᵢ[ℂ] E := K.extendUnitary (LinearIsometryEquiv.refl ℂ K)
    refine ⟨U, fun i => ?_, fun i => ?_, fun x => ?_, ?_⟩
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact K.extendUnitary_apply_twice (LinearIsometryEquiv.refl ℂ K)
        (fun x => rfl) x
    · exact K.finiteDimensional_range_extendUnitary_sub_id
        (LinearIsometryEquiv.refl ℂ K)
  · obtain ⟨deltaTotal, hdeltaTotal, htotal⟩ :=
      exists_delta_gramTransportedWithinInvolution_uniform (n := n) htau
    let delta : ℝ := deltaTotal / ((n : ℝ) * (n : ℝ))
    have hden : 0 < (n : ℝ) * (n : ℝ) := mul_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have hdelta : 0 < delta := div_pos hdeltaTotal hden
    refine ⟨delta, hdelta, ?_⟩
    intro E _ _ v w hv hw horth herr
    haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    obtain ⟨U, hU, hU2, hfinite⟩ := htotal v w hv hw horth (by
      unfold gramError
      calc
        (∑ i, ∑ j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖) <
            ∑ _i : Fin n, ∑ _j : Fin n, delta := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro i _
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro j _
          exact herr i j
        _ = (n : ℝ) * ((n : ℝ) * delta) := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        _ = deltaTotal := by
          dsimp only [delta]
          field_simp)
    refine ⟨U, hU, fun i => ?_, hU2, hfinite⟩
    calc
      ‖U (w i) - v i‖ = ‖U (U (w i) - v i)‖ :=
        (U.norm_map (U (w i) - v i)).symm
      _ = ‖w i - U (v i)‖ := by simp only [map_sub, hU2]
      _ = ‖U (v i) - w i‖ := norm_sub_rev _ _
      _ < tau := hU i

end MathlibAnnex.InnerProductSpace
