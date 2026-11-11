import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.UniversalRepresentation
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.NormalExtension
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FunctionalRealization
import MathlibAnnex.Analysis.CStarAlgebra.CyclicTransport

/-!
# The literal bidual in the all-state universal representation

Every bounded functional is realized as one norm-controlled matrix
coefficient of the all-state representation. The construction uses the
existing nonunital cyclic realization, then transports its cyclic vector
to the canonical GNS coordinate of its vector state. It does not replace
the universal representation by the pure-state sum.

The represented extension used below is the existing map on the literal
`StrongDual ℂ (StrongDual ℂ A)`. Norm and topology conclusions therefore
refer to the actual Banach bidual, without a second abstract bidual model.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section

open Set
open scoped CStarAlgebra ComplexOrder InnerProduct lp

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NonUnitalCStarRepresentation

/-- A norm-one coefficient of two unit vectors forces its source vector
state to have norm one on the original algebra. In particular, no scalar
character of a formal unitization can account for the source vector. -/
theorem norm_matrixCoefficient_self_eq_one_of_norm_matrixCoefficient_eq_one
    (pi : NonUnitalCStarRepresentation A H) (x y : H)
    (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1)
    (hxy : ‖matrixCoefficient pi x y‖ = 1) :
    ‖matrixCoefficient pi x x‖ = 1 := by
  let c : ℝ := ‖matrixCoefficient pi x x‖
  have hc : 0 ≤ c := norm_nonneg _
  have hc1 : c ≤ 1 := by
    simpa only [hx, one_mul] using norm_matrixCoefficient_le pi x x
  have hs (a : A) : ‖pi a x‖ ^ 2 ≤ c * ‖a‖ ^ 2 := by
    calc
      ‖pi a x‖ ^ 2 = ‖matrixCoefficient pi x x (star a * a)‖ := by
        rw [matrixCoefficient_star_mul_self, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (pi a x))]
      _ ≤ c * ‖star a * a‖ := (matrixCoefficient pi x x).le_opNorm _
      _ = c * ‖a‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]
  have hb (a : A) : ‖matrixCoefficient pi x y a‖ ≤ Real.sqrt c * ‖a‖ := by
    have hfirst : ‖matrixCoefficient pi x y a‖ ≤ ‖pi a x‖ := by
      calc
        ‖matrixCoefficient pi x y a‖ ≤ ‖y‖ * ‖pi a x‖ := norm_inner_le_norm _ _
        _ ≤ 1 * ‖pi a x‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg _)
        _ = ‖pi a x‖ := one_mul _
    have hnonneg : 0 ≤ Real.sqrt c * ‖a‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hs' : ‖pi a x‖ ^ 2 ≤ (Real.sqrt c * ‖a‖) ^ 2 := by
      simpa only [mul_pow, Real.sq_sqrt hc] using hs a
    have hsecond : ‖pi a x‖ ≤ Real.sqrt c * ‖a‖ := by
      nlinarith [norm_nonneg (pi a x)]
    exact hfirst.trans hsecond
  have hop : ‖matrixCoefficient pi x y‖ ≤ Real.sqrt c :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hb
  rw [hxy] at hop
  have hroot := Real.sq_sqrt hc
  change c = 1
  nlinarith [Real.sqrt_nonneg c]

variable [PartialOrder A] [StarOrderedRing A]

/-- Pointed transport from an original-algebra cyclic action to the actual
GNS space of its norm-one vector functional. Cyclicity is not assumed only
after adjoining a unit. -/
theorem exists_pointed_stateGNS_transport
    (pi : NonUnitalCStarRepresentation A H) (x : H) (hx : ‖x‖ = 1)
    (hcyclic : DenseRange (fun a : A => pi a x))
    (hstate : matrixCoefficient pi x x ∈ nonUnitalStateSpace A) :
    ∃ W : H ≃ₗᵢ[ℂ] NonUnitalStateGNS.Space (matrixCoefficient pi x x) hstate,
      W x = NonUnitalStateGNS.vector (matrixCoefficient pi x x) hstate ∧
      ∀ (a : A) (z : H), W (pi a z) =
        NonUnitalStateGNS.representation (matrixCoefficient pi x x) hstate a (W z) := by
  let phi := matrixCoefficient pi x x
  let psi := Representation.vectorFunctional pi.unitization x
  have hpsi : psi ∈ stateSpace (Unitization ℂ A) :=
    vectorFunctional_mem_stateSpace pi.unitization x hx
  have hrest : unitizationRestriction psi = phi := by
    ext a
    simp only [psi, phi, unitizationRestriction_apply, Representation.vectorFunctional_apply,
      matrixCoefficient_apply, unitization_inr]
  have hext : psi = unitizationExtension phi :=
    eq_unitizationExtension_of_restriction_eq phi psi hpsi hrest
  have hdense : DenseRange (StarAlgHom.orbitMap pi.unitization x) := by
    intro z
    apply closure_mono (s := Set.range (fun a : A => pi a x)) _ (hcyclic z)
    rintro _ ⟨a, rfl⟩
    exact ⟨Unitization.inr a, unitization_inr_apply pi a x⟩
  obtain ⟨W, hW, _hunique⟩ := StarAlgHom.existsUnique_pointedCyclicTransport
    pi.unitization
    (positiveLinearMapOfMemStateSpace (unitizationExtension phi)
      (unitizationExtension_mem_stateSpace phi hstate)).gnsStarAlgHom
    x (NonUnitalStateGNS.vector phi hstate) hdense
    (denseRange_gnsStarAlgHom_stateGNSVector (unitizationExtension phi)
      (unitizationExtension_mem_stateSpace phi hstate)) (fun z => by
        calc
          inner ℂ x (pi.unitization z x) = psi z := rfl
          _ = unitizationExtension phi z := congrArg (fun f => f z) hext
          _ = inner ℂ (NonUnitalStateGNS.vector phi hstate)
              ((positiveLinearMapOfMemStateSpace (unitizationExtension phi)
                (unitizationExtension_mem_stateSpace phi hstate)).gnsStarAlgHom z
                (NonUnitalStateGNS.vector phi hstate)) :=
            (inner_gnsStarAlgHom_stateGNSVector (unitizationExtension phi)
              (unitizationExtension_mem_stateSpace phi hstate) z).symm)
  refine ⟨W, hW.2.1, ?_⟩
  intro a z
  have h := congrArg (fun T => T z) (hW.2.2 (Unitization.inr a))
  change W (pi.unitization (Unitization.inr a) z) = _ at h
  rw [unitization_inr] at h
  exact h

end NonUnitalCStarRepresentation

variable [PartialOrder A] [StarOrderedRing A]

/-- Every nonzero bounded functional is a norm-scaled coefficient of two
unit vectors in the all-state universal Hilbert space. The vectors are
transported into one actual state GNS summand. -/
theorem exists_unit_universalRepresentation_coefficient
    (f : StrongDual ℂ A) (hf : f ≠ 0) :
    ∃ x y : UniversalHilbertSpace A, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      f = (‖f‖ : ℂ) •
        NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A)) x y := by
  let pi := NonUnitalFunctional.cyclicRepresentation f hf
  let x := NonUnitalFunctional.cyclicSourceVector f hf
  let y := NonUnitalFunctional.cyclicTargetVector f hf
  have hx : ‖x‖ = 1 := NonUnitalFunctional.norm_cyclicSourceVector f hf
  have hy : ‖y‖ = 1 := NonUnitalFunctional.norm_cyclicTargetVector f hf
  have hrecover : f = (‖f‖ : ℂ) • NonUnitalCStarRepresentation.matrixCoefficient pi x y :=
    NonUnitalFunctional.recover_cyclicRepresentation f hf
  have hnorm : ‖NonUnitalCStarRepresentation.matrixCoefficient pi x y‖ = 1 := by
    have hn := congrArg norm hrecover
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg f)] at hn
    apply mul_left_cancel₀ (norm_ne_zero_iff.mpr hf)
    simpa only [mul_one] using hn.symm
  let phi := NonUnitalCStarRepresentation.matrixCoefficient pi x x
  have hphi : phi ∈ nonUnitalStateSpace A := by
    refine ⟨fun a ha => NonUnitalCStarRepresentation.matrixCoefficient_self_nonneg pi x ha, ?_⟩
    exact NonUnitalCStarRepresentation.norm_matrixCoefficient_self_eq_one_of_norm_matrixCoefficient_eq_one
      pi x y hx hy.le hnorm
  obtain ⟨W, _hpoint, hW⟩ := NonUnitalCStarRepresentation.exists_pointed_stateGNS_transport
    pi x hx (NonUnitalFunctional.denseRange_cyclicRepresentation f hf) hphi
  let s : nonUnitalStateSpace A := ⟨phi, hphi⟩
  refine ⟨universalStateEmbedding s (W x), universalStateEmbedding s (W y), ?_, ?_, ?_⟩
  · rw [norm_universalStateEmbedding, W.norm_map, hx]
  · rw [norm_universalStateEmbedding, W.norm_map, hy]
  · rw [matrixCoefficient_universalStateEmbedding,
      NonUnitalCStarRepresentation.matrixCoefficient_eq_of_intertwines pi
        (NonUnitalStateGNS.representation phi hphi) W hW]
    exact hrecover

/-- Exact coefficient realization with the optimal product-of-norms bound,
including the zero functional and the zero C*-algebra. -/
theorem exists_universalRepresentation_coefficient (f : StrongDual ℂ A) :
    ∃ x y : UniversalHilbertSpace A,
      NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A)) x y = f ∧
      ‖x‖ * ‖y‖ ≤ ‖f‖ := by
  by_cases hf : f = 0
  · refine ⟨0, 0, ?_, ?_⟩
    · ext a
      simp only [NonUnitalCStarRepresentation.matrixCoefficient_apply,
        map_zero, inner_zero_left, hf, ContinuousLinearMap.zero_apply]
    · simp only [norm_zero, zero_mul, hf, le_refl]
  · obtain ⟨x, y, hx, hy, hrecover⟩ := exists_unit_universalRepresentation_coefficient f hf
    refine ⟨(‖f‖ : ℂ) • x, y, ?_, ?_⟩
    · calc
        NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A))
            ((‖f‖ : ℂ) • x) y =
            (‖f‖ : ℂ) • NonUnitalCStarRepresentation.matrixCoefficient
              (universalRepresentation (A := A)) x y := by
          ext a
          simp only [NonUnitalCStarRepresentation.matrixCoefficient_apply, map_smul,
            inner_smul_right, ContinuousLinearMap.smul_apply, smul_eq_mul]
        _ = f := hrecover.symm
    · simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg f), hx, hy, mul_one, le_refl]

private theorem representedCoefficient_inner (pi : NonUnitalCStarRepresentation A H) (x y : H) :
    MathlibAnnex.RepresentedBidual.coefficient pi x (innerSL ℂ y) =
      NonUnitalCStarRepresentation.matrixCoefficient pi x y := by
  ext a
  rfl

/-- The existing represented extension preserves the literal Banach-bidual
norm in the all-state universal representation. -/
theorem norm_extension_universalRepresentation (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A)) F‖ = ‖F‖ := by
  let E := MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))
  refine le_antisymm (MathlibAnnex.RepresentedBidual.norm_extension_apply_le _ _) ?_
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (E F))
  intro f
  obtain ⟨x, y, hcoef, hnorm⟩ := exists_universalRepresentation_coefficient f
  have hvalue : F f = inner ℂ y (E F x) := by
    simpa only [E, innerSL_apply_apply, representedCoefficient_inner, hcoef] using
      (MathlibAnnex.RepresentedBidual.coefficient_extension
        (universalRepresentation (A := A)) F x (innerSL ℂ y)).symm
  calc
    ‖F f‖ = ‖inner ℂ y (E F x)‖ := congrArg norm hvalue
    _ ≤ ‖y‖ * ‖E F x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖E F‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left ((E F).le_opNorm x) (norm_nonneg _)
    _ = ‖E F‖ * (‖x‖ * ‖y‖) := by ring
    _ ≤ ‖E F‖ * ‖f‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

/-- Faithfulness here is on the complete literal Banach bidual, rather
than only on the canonical copy of the original algebra. -/
theorem extension_universalRepresentation_injective :
    Function.Injective
      (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))) := by
  intro F G h
  have hzero : MathlibAnnex.RepresentedBidual.extension
      (universalRepresentation (A := A)) (F - G) = 0 := by
    exact (map_sub (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))) F G).trans (sub_eq_zero.mpr h)
  have hn := norm_extension_universalRepresentation (F - G)
  rw [hzero, norm_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp hn.symm)

/-- Isometry of the existing represented extension, without changing the
norm instance on the literal double dual. -/
theorem isometry_extension_universalRepresentation :
    Isometry (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))) := by
  let E : StrongDual ℂ (StrongDual ℂ A) →ₗᵢ[ℂ]
      (UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :=
    { (MathlibAnnex.RepresentedBidual.extension
        (universalRepresentation (A := A))).toLinearMap with
      norm_map' := norm_extension_universalRepresentation }
  exact E.isometry

/-- On this all-state representation, WOT convergence tests contain every
functional of the original Banach dual. The induced topology on its bidual
image is therefore exactly weak-star, even without a boundedness premise. -/
theorem continuous_extension_universalRepresentation_iff
    {X : Type*} [TopologicalSpace X]
    (F : X → WeakDual ℂ (StrongDual ℂ A)) :
    Continuous (fun t => ContinuousLinearMapWOT.ofCLM
      (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))
        (WeakDual.toStrongDual (F t)))) ↔ Continuous F := by
  constructor
  · intro h
    apply WeakDual.continuous_of_continuous_eval
    intro f
    obtain ⟨x, y, hcoef, _hnorm⟩ := exists_universalRepresentation_coefficient f
    have ht := (ContinuousLinearMapWOT.continuous_dual_apply x (innerSL ℂ y)).comp h
    have heq : (fun t => inner ℂ y
        (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))
          (WeakDual.toStrongDual (F t)) x)) = (fun t => F t f) := by
      funext t
      simpa only [innerSL_apply_apply, representedCoefficient_inner, hcoef, WeakDual.toStrongDual_apply] using
        MathlibAnnex.RepresentedBidual.coefficient_extension
          (universalRepresentation (A := A)) (WeakDual.toStrongDual (F t)) x (innerSL ℂ y)
    change Continuous (fun t => F t f)
    rw [← heq]
    exact ht
  · intro h
    exact (MathlibAnnex.RepresentedBidual.extension_weakStar_wotContinuous
      (universalRepresentation (A := A))).comp h

/- The following scalar testers are selected independently for each f.
They are not asserted to be linear in f on all operators. Linearity is
proved only on the WOT closure of the represented original algebra. -/

private def coefficientSource (f : StrongDual ℂ A) : UniversalHilbertSpace A :=
  Classical.choose (exists_universalRepresentation_coefficient f)

private def coefficientTarget (f : StrongDual ℂ A) : UniversalHilbertSpace A :=
  Classical.choose (Classical.choose_spec (exists_universalRepresentation_coefficient f))

private theorem selected_coefficient (f : StrongDual ℂ A) :
    NonUnitalCStarRepresentation.matrixCoefficient (universalRepresentation (A := A))
      (coefficientSource f) (coefficientTarget f) = f ∧
      ‖coefficientSource f‖ * ‖coefficientTarget f‖ ≤ ‖f‖ :=
  Classical.choose_spec (Classical.choose_spec (exists_universalRepresentation_coefficient f))

private def universalScalarEvaluation (f : StrongDual ℂ A)
    (T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A) : ℂ :=
  inner ℂ (coefficientTarget f) (T (coefficientSource f))

private theorem continuous_universalScalarEvaluation (f : StrongDual ℂ A) :
    Continuous (universalScalarEvaluation f) :=
  ContinuousLinearMapWOT.continuous_dual_apply (coefficientSource f)
    (innerSL ℂ (coefficientTarget f))

private theorem universalScalarEvaluation_source (f : StrongDual ℂ A) (a : A) :
    universalScalarEvaluation f
      (ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)) = f a :=
  congrArg (fun g : StrongDual ℂ A => g a) (selected_coefficient f).1

private theorem norm_universalScalarEvaluation_le (f : StrongDual ℂ A)
    (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) :
    ‖universalScalarEvaluation f (ContinuousLinearMapWOT.ofCLM T)‖ ≤ ‖T‖ * ‖f‖ := by
  calc
    ‖universalScalarEvaluation f (ContinuousLinearMapWOT.ofCLM T)‖ ≤
        ‖coefficientTarget f‖ * ‖T (coefficientSource f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖coefficientTarget f‖ * (‖T‖ * ‖coefficientSource f‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖T‖ * (‖coefficientSource f‖ * ‖coefficientTarget f‖) := by ring
    _ ≤ ‖T‖ * ‖f‖ := mul_le_mul_of_nonneg_left (selected_coefficient f).2 (norm_nonneg T)

private theorem universalScalarEvaluation_add
    (T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A)
    (hT : T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))))
    (f g : StrongDual ℂ A) :
    universalScalarEvaluation (f + g) T =
      universalScalarEvaluation f T + universalScalarEvaluation g T := by
  apply closure_minimal ?_ (isClosed_eq (continuous_universalScalarEvaluation (f + g))
    ((continuous_universalScalarEvaluation f).add
      (continuous_universalScalarEvaluation g))) hT
  rintro _ ⟨a, rfl⟩
  simp only [Set.mem_setOf_eq, Pi.add_apply, universalScalarEvaluation_source, ContinuousLinearMap.add_apply]

private theorem universalScalarEvaluation_smul
    (T : UniversalHilbertSpace A →WOT[ℂ] UniversalHilbertSpace A)
    (hT : T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))))
    (c : ℂ) (f : StrongDual ℂ A) :
    universalScalarEvaluation (c • f) T = c • universalScalarEvaluation f T := by
  apply closure_minimal ?_ (isClosed_eq (continuous_universalScalarEvaluation (c • f))
    ((continuous_universalScalarEvaluation f).const_smul c)) hT
  rintro _ ⟨a, rfl⟩
  simp only [Set.mem_setOf_eq, Pi.smul_apply, universalScalarEvaluation_source, ContinuousLinearMap.smul_apply]

/-- A WOT limit of the universal original-algebra range defines an actual
bounded functional on `StrongDual ℂ A`. Linear relations between the chosen
coefficient testers are extended from the source by WOT closedness. -/
def bidualOfUniversalWOTClosure
    (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)))) :
    StrongDual ℂ (StrongDual ℂ A) :=
  LinearMap.mkContinuous
    { toFun f := universalScalarEvaluation f (ContinuousLinearMapWOT.ofCLM T)
      map_add' f g := universalScalarEvaluation_add _ hT f g
      map_smul' c f := universalScalarEvaluation_smul _ hT c f }
    ‖T‖ (fun f => norm_universalScalarEvaluation_le f T)

/-- The constructed literal bidual functional recovers every coefficient
of the given WOT-limit operator, not only its selected scalar testers. -/
theorem bidualOfUniversalWOTClosure_coefficient
    (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))))
    (x : UniversalHilbertSpace A) (g : StrongDual ℂ (UniversalHilbertSpace A)) :
    bidualOfUniversalWOTClosure T hT
        (MathlibAnnex.RepresentedBidual.coefficient (universalRepresentation (A := A)) x g) =
      g (T x) := by
  let f := MathlibAnnex.RepresentedBidual.coefficient (universalRepresentation (A := A)) x g
  change universalScalarEvaluation f (ContinuousLinearMapWOT.ofCLM T) = g (T x)
  apply closure_minimal ?_ (isClosed_eq (continuous_universalScalarEvaluation f)
    (ContinuousLinearMapWOT.continuous_dual_apply x g)) hT
  rintro _ ⟨a, rfl⟩
  change universalScalarEvaluation f
      (ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)) =
    g (universalRepresentation a x)
  rw [universalScalarEvaluation_source]
  rfl

/-- Surjectivity onto the WOT closure is proved by the literal bounded
functional just constructed. No Kaplansky-density premise is inserted. -/
theorem extension_bidualOfUniversalWOTClosure
    (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a)))) :
    MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A))
      (bidualOfUniversalWOTClosure T hT) = T := by
  apply (MathlibAnnex.RepresentedBidual.extension_eq_iff _ _ _).2
  exact bidualOfUniversalWOTClosure_coefficient T hT

/-- The universal represented extension has exactly the WOT-closed
original-algebra range. This statement includes genuinely nonunital and
zero C*-algebras. -/
theorem range_extension_universalRepresentation :
    Set.range (fun F : StrongDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM
        (MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A)) F)) =
      closure (Set.range (fun a : A =>
        ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨F, rfl⟩
    exact MathlibAnnex.RepresentedBidual.extension_mem_wotClosure_range
      (universalRepresentation (A := A)) F
  · intro T hT
    refine ⟨bidualOfUniversalWOTClosure T.toCLM hT, ?_⟩
    simpa only [ContinuousLinearMapWOT.ofCLM_toCLM] using
      congrArg ContinuousLinearMapWOT.ofCLM
        (extension_bidualOfUniversalWOTClosure T.toCLM hT)

/-- Every element of the concrete all-state envelope is the represented
image of an element of the literal Banach bidual. The original-range WOT
closure theorem handles the genuinely nonunital case. -/
theorem exists_extension_eq_of_mem_envelopingVonNeumannAlgebra
    (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A)
    (hT : T ∈ envelopingVonNeumannAlgebra (A := A)) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A),
      MathlibAnnex.RepresentedBidual.extension (universalRepresentation (A := A)) F = T := by
  have hclosure : ContinuousLinearMapWOT.ofCLM T ∈ closure (Set.range (fun a : A =>
      ContinuousLinearMapWOT.ofCLM (universalRepresentation (A := A) a))) := by
    simpa only [← Set.range_comp, Function.comp_def] using
      (mem_envelopingVonNeumannAlgebra_iff_mem_wotClosure T).mp hT
  exact ⟨bidualOfUniversalWOTClosure T hclosure, extension_bidualOfUniversalWOTClosure T hclosure⟩

end MathlibAnnex.Analysis.CStarAlgebra
