import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.NormalStateDomination
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow
import MathlibAnnex.Analysis.Normed.TensorProduct.BidualForms

/-!
# One source net for diagonal bilinear tests and tensor generators

The source sample was chosen using all states and all scalar functionals;
it is independent of a subsequently supplied dominated bilinear test.
Thus finite collections of such tests share the same sample and the same
norm bound. For x = a*, the orientation B(a*,a) is exactly the existing
row generator x tensor x*. Nothing is silently reversed.

The last theorem proves actual weak-star row-closure from a per-functional
source domination supplier. Existence of that supplier for all bounded
forms belongs to lane A and is NOT claimed by this conditional theorem.
C02 unbuilt proof-source candidate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Filter Topology

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.CStarBilinear MathlibAnnex.BidualBilinear
open MathlibAnnex.ProjectiveTensorProduct MathlibAnnex.FiniteApproximation
open MathlibAnnex.CStarAlgebra.TensorAveraging

universe u w
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[simp] theorem bidualStar_sub (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (F - G) = bidualStar F - bidualStar G := by
  ext f
  simp only [bidualStar_apply, ContinuousLinearMap.sub_apply, star_sub]

/-- Diagonal convergence in the KOS orientation, using one a for both slots. -/
theorem tendsto_source_star_diagonal
    (B : A →L[ℂ] A →L[ℂ] ℂ) (phi psi : StateIndex A)
    (C : ℝ) (hC : 0 ≤ C) (hB : IsStrongStarDominated B phi.val psi.val C)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    Tendsto (fun d => B (star (stateSourceNet F d)) (stateSourceNet F d)) atTop
      (𝓝 (BidualForm.eval (firstArens B) (bidualStar F) F)) := by
  have hF : Tendsto (fun d => normalStateGauge phi
      (NormedSpace.inclusionInDoubleDual ℂ A (star (stateSourceNet F d)) - bidualStar F))
      atTop (𝓝 0) := by
    simpa only [stateSourceError, ← bidualStar_canonical, ← bidualStar_sub,
      normalStateGauge_star] using stateSourceError_gauge F phi
  have hG := stateSourceError_gauge F psi
  have hbound : ∀ᶠ d in (atTop : Filter (StateApproxIndex A)),
      normalStateGauge psi (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)) ≤
        2 * ‖F‖ := by
    apply Filter.Eventually.of_forall
    intro d
    calc
      normalStateGauge psi (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)) ≤
          2 * ‖NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)‖ :=
        normalStateGauge_le_two_norm _ _
      _ = 2 * ‖stateSourceNet F d‖ := by
        change 2 * ‖(NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A))
          (stateSourceNet F d)‖ = _
        rw [(NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).norm_map]
      _ ≤ 2 * ‖F‖ := mul_le_mul_of_nonneg_left (stateSourceNet_norm_le F d) (by norm_num)
  have h := tendsto_firstArens_of_state_gauges B phi psi C hC hB atTop
    (fun d => NormedSpace.inclusionInDoubleDual ℂ A (star (stateSourceNet F d))) (bidualStar F)
    (fun d => NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)) F
    hF hG (2 * ‖F‖) hbound
  simpa only [firstArens_canonical] using h

/-- Finitely many tests use one common source element, with a uniform budget. -/
theorem exists_source_finite_diagonal_tests
    {ι : Type w} (s : Finset ι)
    (B : ι → A →L[ℂ] A →L[ℂ] ℂ)
    (phi psi : ι → StateIndex A) (C : ι → ℝ)
    (hC : ∀ i ∈ s, 0 ≤ C i)
    (hB : ∀ i ∈ s, IsStrongStarDominated (B i) (phi i).val (psi i).val (C i))
    (F : StrongDual ℂ (StrongDual ℂ A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖a‖ ≤ ‖F‖ ∧ ∀ i ∈ s,
      ‖B i (star a) a - BidualForm.eval (firstArens (B i)) (bidualStar F) F‖ < ε := by
  classical
  have he : ∀ᶠ d in (atTop : Filter (StateApproxIndex A)), ∀ i ∈ s,
      ‖B i (star (stateSourceNet F d)) (stateSourceNet F d) -
        BidualForm.eval (firstArens (B i)) (bidualStar F) F‖ < ε := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    have ht := (Metric.tendsto_nhds.mp
      (tendsto_source_star_diagonal (B i) (phi i) (psi i) (C i)
        (hC i hi) (hB i hi) F)) ε hε
    simpa only [dist_eq_norm] using ht
  obtain ⟨d, hd⟩ := he.exists
  exact ⟨stateSourceNet F d, stateSourceNet_norm_le F d, hd⟩

/-- Evaluate firstArens at the fixed diagonal pair. This is an actual bounded complex-linear
functional on the tensor dual even before any domination is supplied. -/
def diagonalTensorPoint (F : StrongDual ℂ (StrongDual ℂ A)) :
    StrongDual ℂ (StrongDual ℂ (Tensor A)) :=
  LinearMap.mkContinuous
    { toFun := fun f => BidualForm.eval (firstArens (tensorDualIsometry f)) (bidualStar F) F
      map_add' := by
        intro f g
        change firstArensIsometry (tensorDualIsometry (f + g)) (ULift.up (bidualStar F)) (ULift.up F) = _
        simp only [map_add, ContinuousLinearMap.add_apply, BidualForm.eval]
        rfl
      map_smul' := by
        intro c f
        change firstArensIsometry (tensorDualIsometry (c • f)) (ULift.up (bidualStar F)) (ULift.up F) = _
        simp only [map_smul, ContinuousLinearMap.smul_apply, BidualForm.eval]
        rfl }
    (‖F‖ ^ 2) (by
      intro f
      have h := (firstArens (tensorDualIsometry f)).le_opNorm₂
        (ULift.up (bidualStar F)) (ULift.up F)
      change ‖BidualForm.eval (firstArens (tensorDualIsometry f)) (bidualStar F) F‖ ≤
        ‖firstArens (tensorDualIsometry f)‖ * ‖bidualStar F‖ * ‖F‖ at h
      rw [norm_firstArens,
        (tensorDualIsometry (𝕜 := ℂ) (E := A) (F := A)).norm_map f, norm_bidualStar] at h
      change ‖BidualForm.eval (firstArens (tensorDualIsometry f)) (bidualStar F) F‖ ≤
        ‖F‖ ^ 2 * ‖f‖
      calc
        _ ≤ ‖f‖ * ‖F‖ * ‖F‖ := h
        _ = _ := by ring)

@[simp] theorem diagonalTensorPoint_apply
    (F : StrongDual ℂ (StrongDual ℂ A)) (f : StrongDual ℂ (Tensor A)) :
    diagonalTensorPoint F f =
      BidualForm.eval (firstArens (tensorDualIsometry f)) (bidualStar F) F := rfl

/-- The source tensor has exactly the existing row-generator orientation. -/
def sourceDiagonalTensor (F : StrongDual ℂ (StrongDual ℂ A)) (d : StateApproxIndex A) : Tensor A :=
  tprod ℂ A A (star (stateSourceNet F d)) (stateSourceNet F d)

theorem sourceDiagonalTensor_mem_rowGenerators
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : ‖F‖ ≤ 1) (d : StateApproxIndex A) :
    sourceDiagonalTensor F d ∈ rowGenerators A := by
  refine ⟨star (stateSourceNet F d), ?_, ?_⟩
  · simpa only [norm_star] using (stateSourceNet_norm_le F d).trans hF
  · simp only [sourceDiagonalTensor, star_star]

/-- Precise lane-A boundary: existence of source state controls for each
actual tensor-dual functional. No all-test closure is assumed. -/
theorem diagonalTensorPoint_mem_rowClosure
    (F : StrongDual ℂ (StrongDual ℂ A)) (hF : ‖F‖ ≤ 1)
    (hdom : ∀ f : StrongDual ℂ (Tensor A), ∃ (phi psi : StateIndex A) (C : ℝ),
      0 ≤ C ∧ IsStrongStarDominated (tensorDualIsometry f) phi.val psi.val C) :
    InWeakStarClosure (diagonalTensorPoint F) (rowConvexSet A) := by
  classical
  haveI : (atTop : Filter (StateApproxIndex A)).NeBot := Filter.atTop_neBot
  have ht : Tendsto (fun d => StrongDual.toWeakDual
      (NormedSpace.inclusionInDoubleDual ℂ (Tensor A) (sourceDiagonalTensor F d))) atTop
      (𝓝 (StrongDual.toWeakDual (diagonalTensorPoint F))) := by
    apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
    intro f
    obtain ⟨phi, psi, C, hC, hB⟩ := hdom f
    have hf := tendsto_source_star_diagonal (tensorDualIsometry f) phi psi C hC hB F
    change Tendsto (fun d => f (sourceDiagonalTensor F d)) atTop
      (𝓝 (diagonalTensorPoint F f))
    simpa only [tensorDualIsometry_apply, sourceDiagonalTensor,
      diagonalTensorPoint_apply] using hf
  apply isClosed_closure.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro d
  apply subset_closure
  exact ⟨toWeakSpace ℂ (Tensor A) (sourceDiagonalTensor F d),
    ⟨sourceDiagonalTensor F d,
      (subset_convexHull ℝ (rowGenerators A)) (sourceDiagonalTensor_mem_rowGenerators F hF d), rfl⟩,
    rfl⟩

end MathlibAnnex.RepresentedBidual
