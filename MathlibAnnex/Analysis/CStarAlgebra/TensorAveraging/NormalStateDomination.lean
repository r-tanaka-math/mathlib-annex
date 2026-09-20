import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.StateGaugeSampling
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Domination
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Factorization
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.Arens

/-!
# Lifting actual state domination to the explicit Banach bidual

This is the controller's normal-adapter layer, not a second proof of the
arbitrary-bilinear-form inequality allocated to source lane A.

Given an actual source domination by two states, we prove domination of
its canonical first Arens extension by the same states' actual GNS gauges.
The proof passes to the bidual in the second variable first while the first
variable is canonical, and then in the first variable. It therefore does
not presuppose general Arens regularity or separately weak-star continuity.
The gauges and source approximants are constructed, not input suppliers.

All square evaluations use the explicit C01 first-Arens multiplication and
involution. No global C*-structure on the Banach bidual is assumed.
C02 controller-authored proof-source candidate, not compiled.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped InnerProduct ComplexOrder

namespace MathlibAnnex.RepresentedBidual
open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarBilinear
open MathlibAnnex.BidualBilinear

universe u v w
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {D : Type v} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- Gauge defined by a source state's own GNS, with both star squares. -/
def normalStateGauge (phi : StateIndex A) (F : StrongDual ℂ (StrongDual ℂ A)) : ℝ :=
  Real.sqrt (‖stateOperator phi.val phi.property F
      (stateGNSVector phi.val phi.property)‖ ^ 2 +
    ‖star (stateOperator phi.val phi.property F)
      (stateGNSVector phi.val phi.property)‖ ^ 2)

theorem normalStateGauge_nonneg (phi : StateIndex A)
    (F : StrongDual ℂ (StrongDual ℂ A)) : 0 ≤ normalStateGauge phi F := Real.sqrt_nonneg _

/-- Identification with the actual positive first-Arens square evaluations. -/
theorem normalStateGauge_eq_evaluation (phi : StateIndex A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    normalStateGauge phi F = Real.sqrt
      (‖stateExtension phi.val (arensProduct (bidualStar F) F)‖ +
       ‖stateExtension phi.val (arensProduct F (bidualStar F))‖) := by
  rw [stateExtension_star_square phi.val phi.property,
    stateExtension_reverse_square phi.val phi.property]
  simp [normalStateGauge, norm_pow]

@[simp] theorem normalStateGauge_canonical (phi : StateIndex A) (a : A) :
    normalStateGauge phi (NormedSpace.inclusionInDoubleDual ℂ A a) =
      strongStarGauge phi.val a := by
  rw [normalStateGauge_eq_evaluation]
  simp only [bidualStar_canonical, arensProduct_canonical,
    stateExtension_canonical, strongStarGauge]

@[simp] theorem normalStateGauge_star (phi : StateIndex A)
    (F : StrongDual ℂ (StrongDual ℂ A)) :
    normalStateGauge phi (bidualStar F) = normalStateGauge phi F := by
  simp only [normalStateGauge, stateOperator, extension_bidualStar, star_star,
    add_comm]

@[simp] theorem normalStateGauge_zero (phi : StateIndex A) :
    normalStateGauge phi (0 : StrongDual ℂ (StrongDual ℂ A)) = 0 := by
  simp [normalStateGauge, stateOperator]

/-- A harmless coarse constant, independent of the state or test family. -/
theorem normalStateGauge_le_two_norm (phi : StateIndex A)
    (F : StrongDual ℂ (StrongDual ℂ A)) : normalStateGauge phi F ≤ 2 * ‖F‖ := by
  let xi := stateGNSVector phi.val phi.property
  let T := stateOperator phi.val phi.property F
  have hx : ‖xi‖ = 1 := norm_stateGNSVector phi.val phi.property
  have hT : ‖T‖ ≤ ‖F‖ := norm_extension_apply_le (stateFamily phi) F
  have hf : ‖T xi‖ ≤ ‖F‖ := by
    have h := T.le_opNorm xi
    rw [hx, mul_one] at h
    exact h.trans hT
  have hb : ‖star T xi‖ ≤ ‖F‖ := by
    have h := (star T).le_opNorm xi
    rw [hx, mul_one] at h
    have hs : ‖star T‖ = ‖T‖ := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint.norm_map T)
    exact h.trans (hs.le.trans hT)
  have hsum : 0 ≤ ‖T xi‖ ^ 2 + ‖star T xi‖ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs := Real.sq_sqrt hsum
  change Real.sqrt (‖T xi‖ ^ 2 + ‖star T xi‖ ^ 2) ≤ 2 * ‖F‖
  have hf2 : ‖T xi‖ ^ 2 ≤ ‖F‖ ^ 2 := by gcongr
  have hb2 : ‖star T xi‖ ^ 2 ≤ ‖F‖ ^ 2 := by gcongr
  nlinarith [Real.sqrt_nonneg (‖T xi‖ ^ 2 + ‖star T xi‖ ^ 2), norm_nonneg F]

/-- Both GNS coordinates converge along the actual universal source net. -/
theorem stateSourceNet_gauge (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) :
    Tendsto (fun d => strongStarGauge phi.val (stateSourceNet F d)) atTop
      (𝓝 (normalStateGauge phi F)) := by
  have hv := universalSample_strongStar (StateHilbert (A := A)) stateFamily F
    phi (stateGNSVector phi.val phi.property)
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hv.1.norm.pow 2).add (hv.2.norm.pow 2))
  simpa only [Function.comp_def, ← normalStateGauge_canonical, normalStateGauge, stateOperator,
    extension_canonical, map_star, stateSourceNet, stateFamily] using h

/-- The same net also has vanishing error gauge, not just scalar convergence. -/
theorem stateSourceError_gauge (F : StrongDual ℂ (StrongDual ℂ A))
    (phi : StateIndex A) :
    Tendsto (fun d => normalStateGauge phi (stateSourceError F d)) atTop (𝓝 0) := by
  have hf := stateSourceError_forward F phi (stateGNSVector phi.val phi.property)
  have hb := stateSourceError_backward F phi (stateGNSVector phi.val phi.property)
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((hf.norm.pow 2).add (hb.norm.pow 2))
  simpa only [Function.comp_def, normalStateGauge, stateOperator, stateFamily, extension_bidualStar,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_zero] using h

/-- First pass: only evaluation at B a is used for continuity. -/
theorem firstArens_source_bidual_bound
    (B : A →L[ℂ] D →L[ℂ] ℂ) (phi : StateIndex A) (psi : StateIndex D)
    (C : ℝ) (hB : IsStrongStarDominated B phi.val psi.val C)
    (a : A) (G : StrongDual ℂ (StrongDual ℂ D)) :
    ‖BidualForm.eval (firstArens B) (NormedSpace.inclusionInDoubleDual ℂ A a) G‖ ≤
      C * strongStarGauge phi.val a * normalStateGauge psi G := by
  classical
  have hb : Tendsto (fun d => B a (stateSourceNet G d)) atTop (𝓝 (G (B a))) :=
    universalSample_scalar (StateHilbert (A := D)) stateFamily G (B a)
  have hg := (stateSourceNet_gauge G psi).const_mul (C * strongStarGauge phi.val a)
  change ‖G (B a)‖ ≤ _
  exact le_of_tendsto_of_tendsto hb.norm hg
    (Filter.Eventually.of_forall (fun d => hB a (stateSourceNet G d)))

/-- Second pass: continuity in the first variable is intrinsic to firstArens.
No full W1 or independent extension-existence hypothesis is used. -/
theorem firstArens_normalState_bound
    (B : A →L[ℂ] D →L[ℂ] ℂ) (phi : StateIndex A) (psi : StateIndex D)
    (C : ℝ) (hB : IsStrongStarDominated B phi.val psi.val C)
    (F : StrongDual ℂ (StrongDual ℂ A)) (G : StrongDual ℂ (StrongDual ℂ D)) :
    ‖BidualForm.eval (firstArens B) F G‖ ≤
      C * normalStateGauge phi F * normalStateGauge psi G := by
  classical
  have hb : Tendsto (fun d =>
      BidualForm.eval (firstArens B)
        (NormedSpace.inclusionInDoubleDual ℂ A (stateSourceNet F d)) G)
      atTop (𝓝 (BidualForm.eval (firstArens B) F G)) := by
    exact (continuousFirst_firstArens B G).continuousAt.tendsto.comp
      (stateSourceNet_weakStar F)
  have hg := ((stateSourceNet_gauge F phi).const_mul C).mul_const (normalStateGauge psi G)
  exact le_of_tendsto_of_tendsto hb.norm hg
    (Filter.Eventually.of_forall (fun d =>
      firstArens_source_bidual_bound B phi psi C hB (stateSourceNet F d) G))

/-- A difference estimate with both error terms kept at the same index. -/
theorem firstArens_normalState_difference_bound
    (B : A →L[ℂ] D →L[ℂ] ℂ) (phi : StateIndex A) (psi : StateIndex D)
    (C : ℝ) (hB : IsStrongStarDominated B phi.val psi.val C)
    (F F' : StrongDual ℂ (StrongDual ℂ A)) (G G' : StrongDual ℂ (StrongDual ℂ D)) :
    ‖BidualForm.eval (firstArens B) F G - BidualForm.eval (firstArens B) F' G'‖ ≤
      C * normalStateGauge phi (F - F') * normalStateGauge psi G +
      C * normalStateGauge phi F' * normalStateGauge psi (G - G') := by
  have heq : BidualForm.eval (firstArens B) F G - BidualForm.eval (firstArens B) F' G' =
      BidualForm.eval (firstArens B) (F - F') G +
      BidualForm.eval (firstArens B) F' (G - G') := by
    simp only [firstArens_apply, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (firstArens_normalState_bound B phi psi C hB (F - F') G)
    (firstArens_normalState_bound B phi psi C hB F' (G - G')))

/-- Gauge convergence on bounded sets suffices for the canonical form.
This explicitly exhibits the normality input instead of assuming all
bounded B(H) functionals are normal. -/
theorem tendsto_firstArens_of_state_gauges
    (B : A →L[ℂ] D →L[ℂ] ℂ) (phi : StateIndex A) (psi : StateIndex D)
    (C : ℝ) (hC : 0 ≤ C) (hB : IsStrongStarDominated B phi.val psi.val C)
    {ι : Type w} (l : Filter ι)
    (F : ι → StrongDual ℂ (StrongDual ℂ A)) (F0 : StrongDual ℂ (StrongDual ℂ A))
    (G : ι → StrongDual ℂ (StrongDual ℂ D)) (G0 : StrongDual ℂ (StrongDual ℂ D))
    (hF : Tendsto (fun i => normalStateGauge phi (F i - F0)) l (𝓝 0))
    (hG : Tendsto (fun i => normalStateGauge psi (G i - G0)) l (𝓝 0))
    (K : ℝ) (hK : ∀ᶠ i in l, normalStateGauge psi (G i) ≤ K) :
    Tendsto (fun i => BidualForm.eval (firstArens B) (F i) (G i)) l
      (𝓝 (BidualForm.eval (firstArens B) F0 G0)) := by
  have hb : ∀ᶠ i in l,
      ‖BidualForm.eval (firstArens B) (F i) (G i) -
        BidualForm.eval (firstArens B) F0 G0‖ ≤
      C * normalStateGauge phi (F i - F0) * K +
      C * normalStateGauge phi F0 * normalStateGauge psi (G i - G0) := by
    filter_upwards [hK] with i hi
    apply (firstArens_normalState_difference_bound B phi psi C hB
      (F i) F0 (G i) G0).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hi
        (mul_nonneg hC (normalStateGauge_nonneg _ _))
    · exact le_rfl
  have ht : Tendsto (fun i =>
      C * normalStateGauge phi (F i - F0) * K +
      C * normalStateGauge phi F0 * normalStateGauge psi (G i - G0)) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_add] using
      ((hF.const_mul C).mul_const K).add
        (hG.const_mul (C * normalStateGauge phi F0))
  have hn : Tendsto (fun i =>
      ‖BidualForm.eval (firstArens B) (F i) (G i) -
        BidualForm.eval (firstArens B) F0 G0‖) l (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) hb ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- A source-dominated form really has a separately weak-star continuous
canonical extension, using the already supplied factorization theorem. -/
theorem firstArens_separate_of_state_domination
    (B : A →L[ℂ] D →L[ℂ] ℂ) (phi : StateIndex A) (psi : StateIndex D)
    (C : ℝ) (hC : 0 ≤ C) (hB : IsStrongStarDominated B phi.val psi.val C) :
    SeparatelyWeakStarContinuous (firstArens B) := by
  exact separatelyWeakStarContinuous_firstArens B
    (isWeaklyCompact_of_strongStarDominated B phi.val psi.val C
      phi.property.1 psi.property.1 hC hB)

end MathlibAnnex.RepresentedBidual
