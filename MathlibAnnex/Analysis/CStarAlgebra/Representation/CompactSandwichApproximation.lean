import MathlibAnnex.Analysis.CStarAlgebra.TwoSidedInterpolation
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Norm approximation of rank-one operators from one compact image element

C05 controller source, UNBUILT. No quotient construction, closed-range
claim, spectral projection, or classification of irreducible representations
is used. A finite cover of the compact image is combined with the SAME
norm-controlled two-sided Kadison interpolant. This is enough for the
protected-state argument: exact rank-one surjectivity is not needed.
-/
set_option autoImplicit false
noncomputable section
open Metric Set
open scoped InnerProduct ComplexStarModule
namespace MathlibAnnex.Analysis.CStarAlgebra
universe u v
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- A compact image of the closed unit ball has a finite delta net. -/
private theorem compact_unit_ball_finite_net (C : H →L[ℂ] H)
    (hC : IsCompactOperator C) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ s : Finset H, ∀ x : H, ‖x‖ ≤ 1 →
      ∃ z ∈ s, ‖C x - z‖ < delta := by
  classical
  obtain ⟨K, hK, hCK⟩ := hC.image_closedBall_subset_compact (f := C.toLinearMap) 1
  have hcover : K ⊆ ⋃ z : H, ball z delta := by
    intro x hx
    exact mem_iUnion.mpr ⟨x, mem_ball_self hdelta⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun z : H => ball z delta)
    (fun _ => isOpen_ball) hcover
  refine ⟨s, ?_⟩
  intro x hx
  have hCx : C x ∈ K := hCK ⟨x, by simpa using hx, rfl⟩
  obtain ⟨z, hz, hdist⟩ := mem_iUnion₂.mp (hs hCx)
  exact ⟨z, hz, by simpa [dist_eq_norm] using hdist⟩

/-- Approximate on the compact factor in operator norm. The source element
and its adjoint come from a SINGLE sharp interpolant. -/
theorem Representation.exists_compact_left_approx
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (C B : H →L[ℂ] H) (hC : IsCompactOperator C)
    (hCstar : IsSelfAdjoint C) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ b : A, ‖b‖ ≤ ‖B‖ ∧ ‖C * (pi b - B)‖ < epsilon := by
  classical
  let K : ℝ := 2 * ‖B‖
  let delta : ℝ := epsilon / (2 * (1 + K))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨s, hs⟩ := compact_unit_ball_finite_net C hC hdelta
  obtain ⟨b, hb, hdirect, hadjoint⟩ :=
    exists_norm_le_and_both_eq_finset pi hpi s B
  let D : H →L[ℂ] H := pi (star b) - star B
  have hD : ‖D‖ ≤ K := by
    calc
      ‖D‖ ≤ ‖pi (star b)‖ + ‖star B‖ := norm_sub_le _ _
      _ ≤ ‖b‖ + ‖B‖ := by
        have hpi_eq : pi.toNonUnitalStarAlgHom (star b) = pi (star b) := rfl
        simpa only [hpi_eq, norm_star] using add_le_add_left
          (NonUnitalStarAlgHom.norm_apply_le pi.toNonUnitalStarAlgHom (star b)) ‖star B‖
      _ ≤ K := by dsimp [K]; linarith
  have hDC : ‖D * C‖ ≤ K * delta := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg hK hdelta.le)
    intro x hx
    obtain ⟨z, hz, hnear⟩ := hs x hx.le
    have hDz : D z = 0 := by
      change pi (star b) z - (star B) z = 0
      rw [hadjoint z hz, sub_self]
    calc
      ‖(D * C) x‖ = ‖D (C x - z)‖ := by simp [map_sub, hDz]
      _ ≤ ‖D‖ * ‖C x - z‖ := D.le_opNorm _
      _ ≤ K * delta := mul_le_mul hD hnear.le (norm_nonneg _) hK
  have hstar : star (C * (pi b - B)) = D * C := by
    simp [D, star_mul, star_sub, ← map_star, hCstar.star_eq]
  have hsmall : K * delta < epsilon := by
    dsimp [delta]
    have hd : 0 < 2 * (1 + K) := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hd]
    nlinarith
  refine ⟨b, hb, ?_⟩
  calc
    ‖C * (pi b - B)‖ = ‖D * C‖ := by rw [← hstar, norm_star]
    _ ≤ K * delta := hDC
    _ < epsilon := hsmall

/-- A nonzero compact image suffices for norm-approximating any unit rank-one
projection by actual source elements. There is no exact-preimage assumption. -/
theorem Representation.exists_approx_rankOne_of_compact_image
    (pi : Representation A H) (hpi : StarAlgHom.IsIrreducible pi)
    (k : A) (hk : IsCompactOperator (pi k)) (hk0 : pi k ≠ 0)
    (xi : H) (hxi : ‖xi‖ = 1) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ p0 : A, ‖pi p0 - InnerProductSpace.rankOne ℂ xi xi‖ < epsilon := by
  classical
  let C : H →L[ℂ] H := star (pi k) * pi k
  have hC : IsCompactOperator C := hk.clm_comp (star (pi k))
  have hCstar : IsSelfAdjoint C := by
    rw [isSelfAdjoint_iff]
    simp [C, star_mul]
  have hC0 : C ≠ 0 := by
    intro hzero
    have hn : ‖pi k‖ * ‖pi k‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, ← show C = star (pi k) * pi k from rfl, hzero]
      exact norm_zero
    have hp : 0 < ‖pi k‖ := norm_pos_iff.mpr hk0
    nlinarith
  obtain ⟨y, hy⟩ : ∃ y : H, C y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC0 (ContinuousLinearMap.ext h)
  let v : H := C y
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hy
  let B : H →L[ℂ] H := InnerProductSpace.rankOne ℂ y xi
  let L : H →L[ℂ] H :=
    ((‖v‖ ^ 2 : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ xi v
  have hLv : L v = xi := by
    have hvinner : inner ℂ v v = (‖v‖ ^ 2 : ℂ) := by
      simp only [inner_self_eq_norm_sq_to_K]
      rfl
    have hcast : (‖v‖ ^ 2 : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hv.ne'
    simp [L, InnerProductSpace.rankOne_apply, hvinner, smul_smul, hcast]
  obtain ⟨a, ha, haction, _⟩ :=
    exists_norm_le_and_both_eq_finset pi hpi ({v} : Finset H) L
  have hav : pi a v = xi := (haction v (by simp)).trans hLv
  let r : ℝ := epsilon / (2 * (1 + ‖L‖))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨b, hb, hCb⟩ := pi.exists_compact_left_approx hpi C B hC hCstar hr
  have hCB : pi a * C * B = InnerProductSpace.rankOne ℂ xi xi := by
    ext z
    simp only [ContinuousLinearMap.mul_apply, B, InnerProductSpace.rankOne_apply,
      map_smul]
    change inner ℂ xi z • pi a v = inner ℂ xi z • xi
    rw [hav]
  refine ⟨a * (star k * k) * b, ?_⟩
  have hdiff : pi (a * (star k * k) * b) - InnerProductSpace.rankOne ℂ xi xi =
      pi a * (C * (pi b - B)) := by
    rw [← hCB]
    simp only [map_mul, map_star, C, mul_sub, mul_assoc]
  rw [hdiff]
  calc
    ‖pi a * (C * (pi b - B))‖ ≤ ‖pi a‖ * ‖C * (pi b - B)‖ := norm_mul_le _ _
    _ ≤ ‖L‖ * r := mul_le_mul ((NonUnitalStarAlgHom.norm_apply_le
      pi.toNonUnitalStarAlgHom a).trans ha) hCb.le
      (norm_nonneg _) (norm_nonneg L)
    _ < epsilon := by
      dsimp [r]
      have hd : 0 < 2 * (1 + ‖L‖) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hd]
      nlinarith [norm_nonneg L]

end MathlibAnnex.Analysis.CStarAlgebra
