/- General finite-dimensional-head/Hilbert increment-locality predicate and
projection estimates. The complete-continuity consequence is proved downstream
in Localization/GeneralCriterion. The coordinate specialization is linked by
Localization/CoordinateBridge.
Execution evidence is recorded in the external receipts. -/
import BanachGeometry.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open scoped BigOperators InnerProductSpace
namespace BanachGeometry.LipschitzFreeLocalization
universe uM uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- R6's increment condition: neither target coordinates nor separability of the domain is imposed. -/
def IncrementLocality {M : Type uM} [TopologicalSpace M] (D : M → H) : Prop :=
  ∀ {I : Type} [Fintype I], ∀ z : I → M, Function.Injective z →
    ∃ O : I → Set M, (∀ i, IsOpen (O i) ∧ z i ∈ O i) ∧
    ∃ F : Submodule ℝ H, FiniteDimensional ℝ F ∧
    ∃ K : I → Submodule ℝ H,
      (∀ i, IsClosed (K i : Set H) ∧ K i ≤ Fᗮ) ∧
      (∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) ∧
      ∀ i, ∀ x ∈ O i, ∀ y ∈ O i, D x - D y ∈ F ⊔ K i

/-- In particular, the hypothesis restricts to any compact pointed subset through its inclusion. -/
theorem IncrementLocality.comp {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {D : M → H} (hD : IncrementLocality D) (e : N → M) (he : Continuous e)
    (hi : Function.Injective e) : IncrementLocality (D ∘ e) := by
  intro I _ z hz
  obtain ⟨O, hO, F, hF, K, hK, horth, hinc⟩ := hD (e ∘ z) (hi.comp hz)
  refine ⟨fun i => e ⁻¹' O i, fun i => ⟨(hO i).1.preimage he, (hO i).2⟩,
    F, hF, K, hK, horth, ?_⟩
  intro i x hx y hy
  exact hinc i (e x) hx (e y) hy

/-- Finite Pythagoras without choosing a countable basis or coordinates. -/
theorem norm_sum_sq_of_orthogonal {I : Type*} [Fintype I] (v : I → H)
    (hv : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j _ hji
    exact hv i j (Ne.symm hji)
  · simp

/-- Bessel bound for arbitrary pairwise orthogonal projectable subspaces of H. -/
theorem sum_norm_starProjection_sq_le {I : Type*} [Fintype I]
    (K : I → Submodule ℝ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : ∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0) (b : H) :
    (∑ i, ‖(K i).starProjection b‖ ^ 2) ≤ ‖b‖ ^ 2 := by
  let p : I → H := fun i => (K i).starProjection b
  have hp : ∀ i j, i ≠ j → ⟪p i, p j⟫_ℝ = 0 :=
    fun i j hij => hK i j hij _ ((K i).starProjection_apply_mem b) _ ((K j).starProjection_apply_mem b)
  have hnorm := norm_sum_sq_of_orthogonal p hp
  have hinner : ⟪b, ∑ i, p i⟫_ℝ = ∑ i, ‖p i‖ ^ 2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he := (K i).starProjection_inner_eq_zero b (p i) ((K i).starProjection_apply_mem b)
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at he
    linarith
  have he := norm_sub_sq_real b (∑ i, p i)
  have hn := sq_nonneg ‖b - ∑ i, p i‖
  dsimp [p] at hnorm hinner he hn ⊢
  linarith

/-- A unit vector can have projection norm at least eta on at most eta^-2 such subspaces. -/
theorem card_le_one_div_sq_of_large_projections {I : Type*} [Fintype I]
    (K : I → Submodule ℝ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : ∀ i j, i ≠ j → ∀ u ∈ K i, ∀ v ∈ K j, ⟪u, v⟫_ℝ = 0)
    (b : H) (hb : ‖b‖ ≤ 1) {η : ℝ} (hη : 0 < η)
    (hlarge : ∀ i, η ≤ ‖(K i).starProjection b‖) :
    (Fintype.card I : ℝ) ≤ 1 / η ^ 2 := by
  have hsum : (Fintype.card I : ℝ) * η ^ 2 ≤ ∑ i, ‖(K i).starProjection b‖ ^ 2 := by
    calc
      (Fintype.card I : ℝ) * η ^ 2 = ∑ _i : I, η ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => (sq_le_sq₀ hη.le (norm_nonneg _)).2 (hlarge i))
  have hnorm : ‖b‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg b]
  exact (le_div_iff₀ (sq_pos_of_pos hη)).2
    (hsum.trans ((sum_norm_starProjection_sq_le K hK b).trans hnorm))

/-- The local scalar-test estimate needed after the exceptional projection bound.
It applies to increments in F+K, not to values of D in an assumed coordinate tail. -/
theorem abs_inner_le_projection_norms (F K : Submodule ℝ H)
    [F.HasOrthogonalProjection] [K.HasOrthogonalProjection]
    (hFK : ∀ f ∈ F, ∀ k ∈ K, ⟪f, k⟫_ℝ = 0)
    {v : H} (hv : v ∈ F ⊔ K) (b : H) :
    |⟪v, b⟫_ℝ| ≤ (‖F.starProjection b‖ + ‖K.starProjection b‖) * ‖v‖ := by
  obtain ⟨f, hf, k, hk, hsum⟩ := Submodule.mem_sup.mp hv
  have horth := hFK f hf k hk
  have henergy : ‖v‖ ^ 2 = ‖f‖ ^ 2 + ‖k‖ ^ 2 := by
    rw [← hsum, norm_add_sq_real, horth]
    ring
  have hfn : ‖f‖ ≤ ‖v‖ := by nlinarith [norm_nonneg f, norm_nonneg v, sq_nonneg ‖k‖]
  have hkn : ‖k‖ ≤ ‖v‖ := by nlinarith [norm_nonneg k, norm_nonneg v, sq_nonneg ‖f‖]
  have hfinner : ⟪f, b⟫_ℝ = ⟪f, F.starProjection b⟫_ℝ := by
    have he := F.starProjection_inner_eq_zero b f hf
    rw [inner_sub_left] at he
    calc
      ⟪f, b⟫_ℝ = ⟪b, f⟫_ℝ := real_inner_comm b f
      _ = ⟪F.starProjection b, f⟫_ℝ := sub_eq_zero.mp he
      _ = ⟪f, F.starProjection b⟫_ℝ := real_inner_comm f (F.starProjection b)
  have hkinner : ⟪k, b⟫_ℝ = ⟪k, K.starProjection b⟫_ℝ := by
    have he := K.starProjection_inner_eq_zero b k hk
    rw [inner_sub_left] at he
    calc
      ⟪k, b⟫_ℝ = ⟪b, k⟫_ℝ := real_inner_comm b k
      _ = ⟪K.starProjection b, k⟫_ℝ := sub_eq_zero.mp he
      _ = ⟪k, K.starProjection b⟫_ℝ := real_inner_comm k (K.starProjection b)
  rw [show ⟪v, b⟫_ℝ = ⟪f, b⟫_ℝ + ⟪k, b⟫_ℝ by rw [← hsum, inner_add_left]]
  calc
    |⟪f, b⟫_ℝ + ⟪k, b⟫_ℝ| ≤ |⟪f, b⟫_ℝ| + |⟪k, b⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖f‖ * ‖F.starProjection b‖ + ‖k‖ * ‖K.starProjection b‖ := by
      rw [hfinner, hkinner]
      exact add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖v‖ * ‖F.starProjection b‖ + ‖v‖ * ‖K.starProjection b‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hfn (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hkn (norm_nonneg _))
    _ = (‖F.starProjection b‖ + ‖K.starProjection b‖) * ‖v‖ := by ring

end BanachGeometry.LipschitzFreeLocalization
