import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Cover
import MathlibAnnex.Analysis.CStarAlgebra.NonUnital.RankOneProjection

/-!
# Rank-one operators in the range of a non-unital representation

Once an irreducible representation contains one rank-one projection, dense
orbits and closedness of an injective C-star homomorphism put every rank-one
operator in its range.
-/

set_option autoImplicit false

open Function Set
open scoped InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A vector fixed by a represented projection has dense orbit under the
original non-unital algebra, not merely under its unitization. -/
theorem denseRange_apply_of_isIrreducible_of_fixed
    (pi : NonUnitalCStarRepresentation A H) (hirr : pi.IsIrreducible)
    {p : A} {e : H} (he : e ≠ 0) (hpe : pi p e = e) :
    DenseRange (fun a : A => pi a e) := by
  have hirrU := isIrreducible_unitization pi hirr
  have horbitU : DenseRange (fun z : Unitization ℂ A => pi.unitization z e) :=
    Representation.denseRange_orbitMap_of_isIrreducible pi.unitization hirrU he
  rw [Metric.denseRange_iff] at horbitU ⊢
  intro y epsilon hepsilon
  obtain ⟨z, hz⟩ := horbitU y epsilon hepsilon
  induction z using Unitization.ind with
  | inl_add_inr c a =>
      refine ⟨c • p + a, ?_⟩
      simpa [unitization, hpe] using hz

/-- Algebraic rank-one links obtained from one represented rank-one
projection. -/
theorem map_mul_projection_mul_star_eq_rankOne
    (pi : NonUnitalCStarRepresentation A H)
    {p a b : A} {e : H}
    (hmap : pi p = InnerProductSpace.rankOne ℂ e e) :
    pi (a * p * star b) =
      InnerProductSpace.rankOne ℂ (pi a e) (pi b e) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
    hmap, InnerProductSpace.rankOne_apply, map_smul]
  congr 1
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_right (pi b) e x

/-- If an injective irreducible representation contains one rank-one
projection, then every rank-one operator belongs to its range. -/
theorem exists_preimage_rankOne_of_rankOne_projection
    (pi : NonUnitalCStarRepresentation A H)
    (hirr : pi.IsIrreducible) (hinj : Function.Injective pi)
    {p : A} {e : H} (he : ‖e‖ = 1)
    (hmap : pi p = InnerProductSpace.rankOne ℂ e e) :
    ∀ x y : H, ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y := by
  have hene : e ≠ 0 := by
    intro hzero
    simp [hzero] at he
  have hpe : pi p e = e := by
    rw [hmap]
    simp [InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, he]
  have horbit : DenseRange (fun a : A => pi a e) :=
    denseRange_apply_of_isIrreducible_of_fixed pi hirr hene hpe
  have hclosed : IsClosed (Set.range pi) :=
    (NonUnitalStarAlgHom.isometry pi hinj).isClosedEmbedding.isClosed_range
  have hright (a : A) (y : H) :
      InnerProductSpace.rankOne ℂ (pi a e) y ∈ Set.range pi := by
    exact horbit.induction_on y
      (hclosed.preimage (by fun_prop)) fun b => by
        refine ⟨a * p * star b, ?_⟩
        exact map_mul_projection_mul_star_eq_rankOne pi hmap
  intro x y
  have hx : InnerProductSpace.rankOne ℂ x y ∈ Set.range pi := by
    exact horbit.induction_on x
      (hclosed.preimage (by fun_prop)) fun a => hright a y
  exact hx

/-- Under the genuinely non-unital singleton hypothesis, every rank-one
operator has a preimage in the original algebra. -/
theorem exists_preimage_rankOne_of_singleton [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi) :
    ∀ x y : H, ∃ a : A, pi a = InnerProductSpace.rankOne ℂ x y := by
  obtain ⟨p, _hp, _hpne, ⟨e, he, hmap⟩, _hcompact⟩ :=
    exists_nonzero_projection_rankOne_map pi hsingle
  exact exists_preimage_rankOne_of_rankOne_projection pi hsingle.1
    (injective_of_singleton pi hsingle) he hmap

/-- A finite sum of rank-one operators has a preimage whenever each
rank-one operator does. -/
theorem exists_preimage_sum_rankOne
    (pi : NonUnitalCStarRepresentation A H)
    {I : Type*} [Fintype I]
    (hpre : ∀ x y : H, ∃ a : A,
      pi a = InnerProductSpace.rankOne ℂ x y)
    (x y : I → H) :
    ∃ a : A, pi a = ∑ i, InnerProductSpace.rankOne ℂ (x i) (y i) := by
  choose a ha using fun i => hpre (x i) (y i)
  refine ⟨∑ i, a i, ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ha i

/-- Compact operators on a Hilbert space are norm limits of finite sums of
rank-one operators.  This local formulation targets the closed range of an
injective representation directly. -/
theorem exists_preimage_of_isCompactOperator_of_rankOne_preimages
    (pi : NonUnitalCStarRepresentation A H)
    (hinj : Function.Injective pi)
    (hpre : ∀ x y : H, ∃ a : A,
      pi a = InnerProductSpace.rankOne ℂ x y)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    ∃ a : A, pi a = T := by
  classical
  have hclosed : IsClosed (Set.range pi) :=
    (NonUnitalStarAlgHom.isometry pi hinj).isClosedEmbedding.isClosed_range
  have hclosure : T ∈ closure (Set.range pi) := by
    rw [Metric.mem_closure_iff]
    intro epsilon hepsilon
    let delta : ℝ := epsilon / 2
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    let K : Set H := closure (T '' Metric.closedBall 0 1)
    have hK : IsCompact K := by
      exact hT.isCompact_closure_image_closedBall 1
    obtain ⟨N, hNK, hNfinite, hNcover⟩ :=
      hK.finite_cover_balls hdelta
    let E : Submodule ℂ H := Submodule.span ℂ N
    letI : FiniteDimensional ℂ E :=
      FiniteDimensional.span_of_finite ℂ hNfinite
    letI : E.HasOrthogonalProjection := inferInstance
    let P : H →L[ℂ] H := E.starProjection
    let S : H →L[ℂ] H := P * T
    let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
      stdOrthonormalBasis ℂ E
    have hSsum : S = ∑ i,
        InnerProductSpace.rankOne ℂ ((b i : E) : H)
          (ContinuousLinearMap.adjoint T ((b i : E) : H)) := by
      dsimp [S, P]
      rw [b.starProjection_eq_sum_rankOne, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact InnerProductSpace.rankOne_comp
        ((b i : E) : H) ((b i : E) : H) T
    obtain ⟨a, ha⟩ := exists_preimage_sum_rankOne pi hpre
      (fun i => ((b i : E) : H))
      (fun i => ContinuousLinearMap.adjoint T ((b i : E) : H))
    have hSrange : S ∈ Set.range pi := by
      refine ⟨a, ?_⟩
      exact ha.trans hSsum.symm
    have hunit (x : H) (hx : ‖x‖ ≤ 1) :
        ‖T x - P (T x)‖ < delta := by
      have hTxK : T x ∈ K := by
        apply subset_closure
        exact ⟨x, by simpa using hx, rfl⟩
      have hcovered := hNcover hTxK
      simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball] at hcovered
      obtain ⟨n, hnN, hn⟩ := hcovered
      rw [E.starProjection_minimal]
      refine lt_of_le_of_lt
        (ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
          (⟨n, Submodule.subset_span hnN⟩ : E)) ?_
      simpa [dist_eq_norm] using hn
    have hnorm : ‖T - S‖ ≤ delta := by
      apply ContinuousLinearMap.opNorm_le_bound' (T - S) hdelta.le
      intro x hxne
      let z : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x
      have hxpos : 0 < ‖x‖ :=
        norm_pos_iff.mpr (norm_ne_zero_iff.mp hxne)
      have hz : ‖z‖ = 1 := by
        simp [z, norm_smul, hxpos.ne']
      have hzbound : ‖T z - P (T z)‖ < delta := hunit z hz.le
      have hxrepr : x = ((‖x‖ : ℝ) : ℂ) • z := by
        simp [z, hxpos.ne']
      change ‖(T - P * T) x‖ ≤ delta * ‖x‖
      have hmaprepr : (T - P * T) x =
          ((‖x‖ : ℝ) : ℂ) • (T - P * T) z := by
        calc
          (T - P * T) x =
              (T - P * T) (((‖x‖ : ℝ) : ℂ) • z) :=
            congrArg (T - P * T) hxrepr
          _ = ((‖x‖ : ℝ) : ℂ) • (T - P * T) z := map_smul _ _ _
      rw [hmaprepr, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      have herr : ‖(T - P * T) z‖ < delta := by
        simpa [mul_apply_eq_comp] using hzbound
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left herr.le (norm_nonneg x)
    refine ⟨S, hSrange, ?_⟩
    rw [dist_eq_norm]
    exact hnorm.trans_lt (by dsimp [delta]; linarith)
  rw [hclosed.closure_eq] at hclosure
  exact hclosure

/-- The compact operators are contained in the range of a genuinely
non-unital singleton model. -/
theorem exists_preimage_of_compact_singleton [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A]
    [TopologicalSpace.SeparableSpace H]
    (pi : NonUnitalCStarRepresentation A H)
    (hsingle : IsSingletonIrreducibleModel.{u, v, u} pi)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) :
    ∃ a : A, pi a = T := by
  apply exists_preimage_of_isCompactOperator_of_rankOne_preimages pi
    (injective_of_singleton pi hsingle)
    (exists_preimage_rankOne_of_singleton pi hsingle) T hT

end NonUnitalCStarRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
