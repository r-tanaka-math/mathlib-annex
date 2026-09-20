import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.InfiniteIndex
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.Compression
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.EscapeGauge

/-!
# One actual isometry with a small common range projection

C06, UNBUILT. All test functionals share the same finite tail and the same
bounded operator on all of H. No statement of nuclearity, separability,
amenability or existence of a desired isometry is used as a premise.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Filter Topology
open scoped InnerProductSpace ComplexOrder CStarAlgebra
namespace MathlibAnnex.FiniteCentral
open MathlibAnnex.RepresentedCentralCorner MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarAlgebra.TensorAveraging
universe u v w t
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type w} [Infinite ι]
variable (b : HilbertBasis ι ℂ H)

/-- Orthogonality is first checked on the basis, then extended to all H. -/
theorem projection_mul_basisEmbedding_eq_zero (s : Finset ι) (e : ι ↪ ι)
    (he : ∀ i, e i ∉ s) :
    coordinateProjection b s * (basisEmbedding b e).toContinuousLinearMap = 0 := by
  apply operator_ext_basis b
  intro i
  simp [ContinuousLinearMap.mul_apply, basisEmbedding_basis, he i]

/-- Orthogonal projections have a positive complementary difference. -/
theorem range_projection_le_tail (s : Finset ι) (w : H →L[ℂ] H)
    (hw : star w * w = 1) (hPw : coordinateProjection b s * w = 0) :
    w * star w ≤ 1 - coordinateProjection b s := by
  let P := coordinateProjection b s
  let r := w * star w
  have hrstar : star r = r := by simp [r]
  have hr2 : r * r = r := by
    dsimp [r]
    calc
      _ = w * (star w * w) * star w := by noncomm_ring
      _ = w * star w := by rw [hw, mul_one]
  have hPr : P * r = 0 := by
    dsimp [P, r]
    rw [← mul_assoc, hPw, zero_mul]
  have hrP : r * P = 0 := by
    have h := congrArg star hPr
    simpa only [star_mul, hrstar, P, star_coordinateProjection, star_zero] using h
  have hstar : star (1 - P - r) = 1 - P - r := by simp [P, hrstar]
  have hidem : (1 - P - r) * (1 - P - r) = 1 - P - r := by
    have hP2 : P * P = P := coordinateProjection_idempotent b s
    simp only [sub_mul, mul_sub, one_mul, mul_one, hP2, hr2, hPr, hrP, mul_zero, zero_mul]
    abel
  have hpos : 0 ≤ 1 - P - r := by
    have h := star_mul_self_nonneg (1 - P - r)
    rwa [hstar, hidem] at h
  exact sub_nonneg.mp hpos

/-- The range may be proper: only star w*w=1 is asserted. -/
theorem exists_isometry_range_le_tail (s : Finset ι) :
    ∃ w : H →L[ℂ] H, star w * w = 1 ∧
      w * star w ≤ 1 - coordinateProjection b s := by
  obtain ⟨e, he⟩ := exists_embedding_avoiding_finset s
  let w := (basisEmbedding b e).toContinuousLinearMap
  have hw : star w * w = 1 := star_mul_of_linearIsometry _
  exact ⟨w, hw, range_projection_le_tail b s w hw
    (projection_mul_basisEmbedding_eq_zero b s e he)⟩

/-- Norm-monotonicity for the positive functional values used in the range
budget. Neither value is silently normalized to one. -/
theorem positive_value_norm_mono (phi : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hp : ∀ T, 0 ≤ T → 0 ≤ phi T)
    {T U : H →L[ℂ] H} (hT : 0 ≤ T) (hTU : T ≤ U) :
    ‖phi T‖ ≤ ‖phi U‖ := by
  have hm : phi T ≤ phi U := by
    have h := hp (U - T) (sub_nonneg.mpr hTU)
    rw [map_sub] at h
    exact sub_nonneg.mp h
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le (hp T hT) hm

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- All normal positive controls share ONE actual range projection. -/
theorem exists_common_escaping_isometry {J : Type t} [Fintype J]
    (b : HilbertBasis ι ℂ H) (phi psi : J → StateIndex A)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ w : H →L[ℂ] H, star w * w = 1 ∧ ∀ j,
      ‖cornerFunctional pi hpi (phi j).val (w * star w)‖ < eta ∧
      ‖cornerFunctional pi hpi (psi j).val (w * star w)‖ < eta := by
  obtain ⟨s, hs⟩ := exists_common_small_tail b pi hpi
    (fun j => (phi j).val) (fun j => (psi j).val) heta
  obtain ⟨w, hw, hwr⟩ := exists_isometry_range_le_tail b s
  refine ⟨w, hw, fun j => ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_lt
      (positive_value_norm_mono (cornerFunctional pi hpi (phi j).val)
        (cornerFunctional_positive pi hpi (phi j).val (phi j).property)
        (mul_star_self_nonneg w) hwr) (hs j).1
  · exact lt_of_le_of_lt
      (positive_value_norm_mono (cornerFunctional pi hpi (psi j).val)
        (cornerFunctional_positive pi hpi (psi j).val (psi j).property)
        (mul_star_self_nonneg w) hwr) (hs j).2

end MathlibAnnex.FiniteCentral
