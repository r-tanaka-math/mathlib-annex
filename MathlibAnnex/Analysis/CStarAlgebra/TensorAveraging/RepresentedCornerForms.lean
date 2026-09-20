import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedCornerGauge
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.BidualPullback
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.MeanCentrality
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorMomentForm

/-!
# The actual bounded-linear tensor-test assignment for an irreducible corner

The formerly input map j is now the constructed isometric central section.
The assignment E is linear/contractive in the arbitrary tensor-dual test and
has the exact two covariance identities. Represented matrix-coefficient
moments are recovered in the same pi/H/vectors. No mean is created here.

Caution: for arbitrary f and nonfaithful pi, E(f)(pi a,pi b) need NOT equal
f(a⊗b): it is the central-corner compression of the canonical bidual form.
This is the map the mean construction needs, not a false descent of every f.
C03 proof-source candidate, unbuilt.
-/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Filter Topology
open scoped InnerProductSpace CStarAlgebra ComplexOrder

namespace MathlibAnnex.RepresentedCentralCorner
open MathlibAnnex.CStarBidual MathlibAnnex.RepresentedBidual
open MathlibAnnex.BidualBilinear MathlibAnnex.FiniteApproximation
open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.CStarAlgebra.TensorAveraging
open MathlibAnnex.CStarBilinear MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.WeakCompact
universe u v t
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]
variable (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)

/-- Adapter into the old, unchanged ULift bidual model. -/
def modelSection : (H →L[ℂ] H) →L[ℂ] BidualModel ℂ A :=
  (bidualModelEquiv ℂ A).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (rawSection pi hpi)

@[simp] theorem modelSection_down (T : H →L[ℂ] H) :
    (modelSection pi hpi T).down = rawSection pi hpi T := rfl

@[simp] theorem norm_modelSection (T : H →L[ℂ] H) :
    ‖modelSection pi hpi T‖ = ‖T‖ := by
  change ‖rawSection pi hpi T‖ = ‖T‖
  exact norm_rawSection pi hpi T

theorem norm_modelSection_le_one : ‖modelSection pi hpi‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  simp only [norm_modelSection, one_mul, le_refl]

/-- One actual operator-bilinear form for each source form. -/
def representedForm (B : A →L[ℂ] A →L[ℂ] ℂ) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) →L[ℂ] ℂ :=
  bilinearPullback (modelSection pi hpi) (firstArens B)

@[simp] theorem representedForm_apply (B : A →L[ℂ] A →L[ℂ] ℂ)
    (X Y : H →L[ℂ] H) :
    representedForm pi hpi B X Y =
      BidualForm.eval (firstArens B) (rawSection pi hpi X) (rawSection pi hpi Y) := rfl

/-- E is an actual bounded-linear family, not a collection of independently
chosen extension witnesses. -/
def tensorAssignment : StrongDual ℂ (Tensor A) →L[ℂ] ContinuousBilinearForm (H →L[ℂ] H) :=
  tensorBidualPullback (modelSection pi hpi)

@[simp] theorem tensorAssignment_apply (f : StrongDual ℂ (Tensor A))
    (X Y : H →L[ℂ] H) :
    tensorAssignment pi hpi f X Y = representedForm pi hpi (tensorDualIsometry f) X Y := rfl

theorem norm_tensorAssignment_apply_le (f : StrongDual ℂ (Tensor A)) :
    ‖tensorAssignment pi hpi f‖ ≤ ‖f‖ := by
  have hj : ‖modelSection pi hpi‖ ^ 2 ≤ 1 := by
    nlinarith [norm_modelSection_le_one pi hpi, norm_nonneg (modelSection pi hpi)]
  exact (norm_tensorBidualPullback_apply_le (modelSection pi hpi) f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (norm_nonneg f))

/-- Pointwise operator-norm contraction, retaining the full uniform bound. -/
theorem norm_tensorAssignment_le_one (f : StrongDual ℂ (Tensor A)) :
    ‖tensorAssignment pi hpi f‖ ≤ ‖f‖ :=
  norm_tensorAssignment_apply_le pi hpi f

private theorem bidual_id (F : StrongDual ℂ (StrongDual ℂ A)) :
    bidualMap (ContinuousLinearMap.id ℂ A) F = F := by
  ext f
  rfl

private theorem section_left_bidual (a : A) (X : H →L[ℂ] H) :
    bidualMap (leftMul ℂ A a) (rawSection pi hpi X) =
      rawSection pi hpi (pi a * X) := by
  change bidualMap (ContinuousLinearMap.mul ℂ A a) (rawSection pi hpi X) = _
  rw [← arensProduct_canonical_left]
  change Model.toRaw A (Model.canonical A a * sectionMap pi hpi X) =
    Model.toRaw A (sectionMap pi hpi (pi a * X))
  rw [left_covariance]

private theorem section_right_bidual (a : A) (Y : H →L[ℂ] H) :
    bidualMap (rightMul ℂ A a) (rawSection pi hpi Y) =
      rawSection pi hpi (Y * pi a) := by
  change bidualMap ((ContinuousLinearMap.mul ℂ A).flip a) (rawSection pi hpi Y) = _
  rw [← arensProduct_canonical_right]
  change Model.toRaw A (sectionMap pi hpi Y * Model.canonical A a) =
    Model.toRaw A (sectionMap pi hpi (Y * pi a))
  rw [right_covariance]

/-- Left action is on the first factor a*x. The identity is valid for every
f, with no unproved arbitrary-bilinear regularity assumption. -/
theorem tensorAssignment_left (a : A) (f : StrongDual ℂ (Tensor A)) :
    tensorAssignment pi hpi (f.comp (leftAction ℂ A a)) =
      leftForm (H →L[ℂ] H) (pi a) (tensorAssignment pi hpi f) := by
  have hB : tensorDualIsometry (f.comp (leftAction ℂ A a)) =
      precompRight ((tensorDualIsometry f).comp (leftMul ℂ A a))
        (ContinuousLinearMap.id ℂ A) := by
    ext x y
    simp only [tensorDualIsometry_apply, ContinuousLinearMap.comp_apply,
      leftAction_tprod, precompRight_apply, leftMul_apply, ContinuousLinearMap.id_apply]
  ext X Y
  change BidualForm.eval (firstArens (tensorDualIsometry (f.comp (leftAction ℂ A a))))
    (rawSection pi hpi X) (rawSection pi hpi Y) =
      BidualForm.eval (firstArens (tensorDualIsometry f))
        (rawSection pi hpi (pi a * X)) (rawSection pi hpi Y)
  rw [hB, firstArens_precomp_apply, bidual_id, section_left_bidual]

/-- Right action is on the second factor y*a, not a*y. -/
theorem tensorAssignment_right (a : A) (f : StrongDual ℂ (Tensor A)) :
    tensorAssignment pi hpi (f.comp (rightAction ℂ A a)) =
      rightForm (H →L[ℂ] H) (pi a) (tensorAssignment pi hpi f) := by
  have hB : tensorDualIsometry (f.comp (rightAction ℂ A a)) =
      precompRight ((tensorDualIsometry f).comp (ContinuousLinearMap.id ℂ A))
        (rightMul ℂ A a) := by
    ext x y
    simp only [tensorDualIsometry_apply, ContinuousLinearMap.comp_apply,
      rightAction_tprod, precompRight_apply, rightMul_apply, ContinuousLinearMap.id_apply]
  ext X Y
  change BidualForm.eval (firstArens (tensorDualIsometry (f.comp (rightAction ℂ A a))))
    (rawSection pi hpi X) (rawSection pi hpi Y) =
      BidualForm.eval (firstArens (tensorDualIsometry f))
        (rawSection pi hpi X) (rawSection pi hpi (Y * pi a))
  rw [hB, firstArens_precomp_apply, bidual_id, section_right_bidual]

/-- The multiplication moment is recovered exactly for the same pi and both
vectors. Arbitrary source tests are not asserted to descend through pi. -/
theorem tensorAssignment_matrixCoefficient (eta xi : H) :
    tensorAssignment pi hpi (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) =
      mulForm (H →L[ℂ] H) (operatorMatrixCoefficient H eta xi) := by
  have hB : tensorDualIsometry (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi) =
      multiplicationForm (coefficient pi.toNonUnitalStarAlgHom xi (innerSL ℂ eta)) := by
    ext a b
    rw [tensorDualIsometry_apply, matrixCoefficient_apply, representedProduct_tprod]
    rfl
  ext X Y
  change BidualForm.eval
    (firstArens (tensorDualIsometry (matrixCoefficient A H pi.toNonUnitalStarAlgHom eta xi)))
      (rawSection pi hpi X) (rawSection pi hpi Y) = inner ℂ eta ((X * Y) xi)
  rw [hB, ← arensProduct_eq_firstArens, ← coefficient_extension,
    extension_arensProduct]
  have hX : extension pi.toNonUnitalStarAlgHom (rawSection pi hpi X) = X :=
    quotient_section pi hpi X
  have hY : extension pi.toNonUnitalStarAlgHom (rawSection pi hpi Y) = Y :=
    quotient_section pi hpi Y
  rw [hX, hY]
  rfl

/-- Actual simultaneous strong-star continuity after supplying source-state
domination. This input is weaker than A's remaining full analytic theorem,
but is not hidden or assumed to have been received. -/
theorem tendsto_representedForm
    (B : A →L[ℂ] A →L[ℂ] ℂ) (phi psi : StateIndex A)
    (C : ℝ) (hC : 0 ≤ C) (hB : IsStrongStarDominated B phi.val psi.val C)
    {ι : Type t} (l : Filter ι) (X Y : ι → H →L[ℂ] H) (X0 Y0 : H →L[ℂ] H)
    (hX : ∀ xi, Tendsto (fun i => X i xi) l (𝓝 (X0 xi)))
    (hXs : ∀ xi, Tendsto (fun i => star (X i) xi) l (𝓝 (star X0 xi)))
    (hY : ∀ xi, Tendsto (fun i => Y i xi) l (𝓝 (Y0 xi)))
    (hYs : ∀ xi, Tendsto (fun i => star (Y i) xi) l (𝓝 (star Y0 xi)))
    (r s : ℝ) (hr : ∀ᶠ i in l, ‖X i‖ ≤ r) (hs : ∀ᶠ i in l, ‖Y i‖ ≤ s) :
    Tendsto (fun i => representedForm pi hpi B (X i) (Y i)) l
      (𝓝 (representedForm pi hpi B X0 Y0)) := by
  have hb : ∀ᶠ i in l, normalStateGauge psi (rawSection pi hpi (Y i)) ≤ 2 * |s| := by
    filter_upwards [hs] with i hi
    calc
      normalStateGauge psi (rawSection pi hpi (Y i)) ≤ 2 * ‖rawSection pi hpi (Y i)‖ :=
        normalStateGauge_le_two_norm psi _
      _ = 2 * ‖Y i‖ := by rw [norm_rawSection]
      _ ≤ 2 * |s| := mul_le_mul_of_nonneg_left (hi.trans (le_abs_self s)) (by norm_num)
  exact tendsto_firstArens_of_state_gauges B phi psi C hC hB l
    (fun i => rawSection pi hpi (X i)) (rawSection pi hpi X0)
    (fun i => rawSection pi hpi (Y i)) (rawSection pi hpi Y0)
    (tendsto_normalStateGauge_section_error pi hpi l X X0 hX hXs r hr phi)
    (tendsto_normalStateGauge_section_error pi hpi l Y Y0 hY hYs s hs psi)
    (2 * |s|) hb

end MathlibAnnex.RepresentedCentralCorner
