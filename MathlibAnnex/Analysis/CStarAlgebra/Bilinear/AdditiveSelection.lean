import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.FiniteMinimax
import MathlibAnnex.Analysis.CStarAlgebra.Bilinear.StateSelection

/-!
# Additive state selection and rescaling

This file isolates the separation/rescaling part of the finite-family
noncommutative Grothendieck argument.  Its analytic input is a weighted
finite additive estimate.  Sion's theorem selects the *same* four states for
all members of a finite family; compactness then selects four states for all
pairs.  Finally, positive real rescaling turns the additive estimate into
the squared product estimate expected by `StateSelection.lean`.

The weighted analytic estimate remains a named premise.  In particular,
this file does not disguise the deep sequence inequality as a state-space
or compactness lemma.
-/

set_option autoImplicit false

open Finset Set
open scoped ComplexOrder

namespace MathlibAnnex.CStarBilinear

open MathlibAnnex.Analysis.CStarAlgebra

universe uA uD uι

noncomputable section

variable {A : Type uA} [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
variable {D : Type uD} [CStarAlgebra D]
  [PartialOrder D] [StarOrderedRing D]

local instance additiveSelectionWeakDualIsScalarTowerA :
    IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance additiveSelectionWeakDualIsScalarTowerD :
    IsScalarTower ℝ ℂ (WeakDual ℂ D) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ D))

local instance additiveSelectionWeakDualLocallyConvexSpaceA :
    LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

local instance additiveSelectionWeakDualLocallyConvexSpaceD :
    LocallyConvexSpace ℝ (WeakDual ℂ D) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ D)))

local instance additiveSelectionWeakDualContinuousRealSMulA :
    ContinuousSMul ℝ (WeakDual ℂ A) :=
  WeakDual.instContinuousSMul ℝ

local instance additiveSelectionWeakDualContinuousRealSMulD :
    ContinuousSMul ℝ (WeakDual ℂ D) :=
  WeakDual.instContinuousSMul ℝ

local instance additiveSelectionStateControlContinuousRealSMul :
    ContinuousSMul ℝ (StateControl A D) :=
  Prod.continuousSMul

@[simp]
private theorem weakDual_add_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f g : WeakDual ℂ E) (x : E) :
    (f + g) x = f x + g x :=
  rfl

@[simp]
private theorem weakDual_real_smul_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (a : ℝ) (f : WeakDual ℂ E) (x : E) :
    (a • f) x = a • f x :=
  rfl

@[simp]
private theorem weakDual_apply_real_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : WeakDual ℂ E) (a : ℝ) (x : E) :
    f (a • x) = a • f x := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
  exact RCLike.real_smul_eq_coe_smul a (f x) |>.symm

/-- A unital C-star algebra with a nonzero unit has a state.  This is kept
explicit because a normalized state cannot exist on the zero algebra. -/
theorem weakStateSpace_nonempty [Nontrivial A] :
    (weakStateSpace A).Nonempty := by
  have hclosed : IsClosed ((⊥ : TwoSidedIdeal A) : Set A) := by
    simpa using (isClosed_singleton : IsClosed ({0} : Set A))
  obtain ⟨phi, hphi⟩ :=
    weakStateFace_nonempty (⊥ : TwoSidedIdeal A) bot_ne_top hclosed
  exact ⟨phi, hphi.1⟩

theorem stateControls_nonempty [Nontrivial A] [Nontrivial D] :
    (stateControls (A := A) (D := D)).Nonempty :=
  ((weakStateSpace_nonempty (A := A)).prod
    (weakStateSpace_nonempty (A := A))).prod
      ((weakStateSpace_nonempty (A := D)).prod
        (weakStateSpace_nonempty (A := D)))

theorem convex_stateControls :
    Convex ℝ (stateControls (A := A) (D := D)) :=
  (convex_weakStateSpace.prod convex_weakStateSpace).prod
    (convex_weakStateSpace.prod convex_weakStateSpace)

theorem leftSquare_nonneg {z : StateControl A D}
    (hz : z ∈ stateControls (A := A) (D := D)) (x : A) :
    0 ≤ leftSquare z x := by
  have hxright : 0 ≤ x * star x := by
    simpa only [star_star] using star_mul_self_nonneg (star x)
  exact add_nonneg
    (RCLike.nonneg_iff.mp (hz.1.1.1 _ (star_mul_self_nonneg x))).1
    (RCLike.nonneg_iff.mp (hz.1.2.1 _ hxright)).1

theorem rightSquare_nonneg {z : StateControl A D}
    (hz : z ∈ stateControls (A := A) (D := D)) (y : D) :
    0 ≤ rightSquare z y := by
  have hyright : 0 ≤ y * star y := by
    simpa only [star_star] using star_mul_self_nonneg (star y)
  exact add_nonneg
    (RCLike.nonneg_iff.mp (hz.2.1.1 _ (star_mul_self_nonneg y))).1
    (RCLike.nonneg_iff.mp (hz.2.2.1 _ hyright)).1

/-- The affine, additive violation tested before the AM--GM rescaling step. -/
def additiveViolation (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (xy : A × D) (z : StateControl A D) : ℝ :=
  ‖B xy.1 xy.2‖ -
    (C / 2) * (leftSquare z xy.1 + rightSquare z xy.2)

/-- Closed additive constraint for one input pair. -/
def additiveControlSet (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (xy : A × D) : Set (StateControl A D) :=
  {z | additiveViolation B C xy z ≤ 0}

theorem continuous_additiveViolation
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D) :
    Continuous (additiveViolation B C xy) := by
  unfold additiveViolation
  exact continuous_const.sub
    (continuous_const.mul
      ((continuous_leftSquare xy.1).add (continuous_rightSquare xy.2)))

theorem isClosed_additiveControlSet
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D) :
    IsClosed (additiveControlSet B C xy) := by
  exact isClosed_Iic.preimage (continuous_additiveViolation B C xy)

theorem additiveViolation_affine
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D)
    (z w : StateControl A D) (a b : ℝ) :
    additiveViolation B C xy (a • z + b • w) =
      a * additiveViolation B C xy z +
        b * additiveViolation B C xy w +
          (1 - a - b) * ‖B xy.1 xy.2‖ := by
  simp only [additiveViolation, leftSquare, rightSquare, Prod.smul_fst,
    Prod.smul_snd, Prod.fst_add, Prod.snd_add, weakDual_add_apply,
    weakDual_real_smul_apply, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem convexOn_additiveViolation
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (xy : A × D) :
    ConvexOn ℝ (stateControls (A := A) (D := D))
      (additiveViolation B C xy) := by
  refine ⟨convex_stateControls, ?_⟩
  intro z _ w _ a b _ _ hab
  rw [additiveViolation_affine B C xy z w a b]
  have hzero : 1 - a - b = 0 := by linarith
  simp only [hzero, zero_mul, add_zero, smul_eq_mul]
  exact le_rfl

/-- The exact analytic input consumed by finite minimax selection.  It says
that every probability-weighted finite average of additive violations can
be controlled by one quadruple of states.  The states may depend on the
weights, but not on an individual summand. -/
def HasWeightedFiniteAdditiveEstimate
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ {ι : Type (max uA uD)} [Fintype ι] [Nonempty ι]
    (x : ι → A) (y : ι → D) (w : ι → ℝ),
      w ∈ stdSimplex ℝ ι →
        ∃ z ∈ stateControls (A := A) (D := D),
          weightedViolation
            (fun i z ↦ additiveViolation B C (x i, y i) z) z w ≤ 0

/-- Sion's theorem upgrades the weighted-average estimate to one quadruple
of states satisfying every member of a nonempty indexed family. -/
theorem exists_common_additiveControl_of_weighted
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C)
    {ι : Type (max uA uD)} [Fintype ι] [Nonempty ι]
    (x : ι → A) (y : ι → D) :
    ∃ z ∈ stateControls (A := A) (D := D),
      ∀ i, z ∈ additiveControlSet B C (x i, y i) := by
  letI : ContinuousSMul ℝ (StateControl A D) :=
    additiveSelectionStateControlContinuousRealSMul
  simpa only [additiveControlSet, mem_setOf_eq] using
    (exists_forall_nonpos_of_weightedViolation
      (E := StateControl A D) (ι := ι)
      (stateControls_nonempty (A := A) (D := D))
      (convex_stateControls (A := A) (D := D))
      (isCompact_stateControls (A := A) (D := D))
      additiveSelectionStateControlContinuousRealSMul
      (fun i z ↦ additiveViolation B C (x i, y i) z)
      (fun i ↦ continuous_additiveViolation B C (x i, y i))
      (fun i ↦ convexOn_additiveViolation B C (x i, y i))
      (fun w hw ↦ hweighted x y w hw))

/-- Empty families are handled from explicit state-space nonemptiness;
nonempty families use the indexed minimax result. -/
theorem finite_additiveControl_of_weighted
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ additiveControlSet B C xy := by
  intro s
  by_cases hs : s.Nonempty
  · let ι := {xy : A × D // xy ∈ s}
    letI : Nonempty ι :=
      ⟨⟨hs.choose, hs.choose_spec⟩⟩
    obtain ⟨z, hz, hall⟩ :=
      exists_common_additiveControl_of_weighted B C hweighted
        (fun i : ι ↦ i.1.1) (fun i : ι ↦ i.1.2)
    refine ⟨z, hz, fun xy hxy ↦ ?_⟩
    exact hall ⟨xy, hxy⟩
  · obtain ⟨z, hz⟩ := stateControls_nonempty (A := A) (D := D)
    refine ⟨z, hz, ?_⟩
    intro xy hxy
    exact (hs ⟨xy, hxy⟩).elim

/-- Compactness upgrades finite common additive controls to four states
working for every pair. -/
theorem exists_global_additiveControl_of_weighted
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    ∃ z ∈ stateControls (A := A) (D := D),
      ∀ x y, ‖B x y‖ ≤
        (C / 2) * (leftSquare z x + rightSquare z y) := by
  have hfinite := finite_additiveControl_of_weighted B C hweighted
  have hne :
      ((stateControls (A := A) (D := D)) ∩
        ⋂ xy : A × D, additiveControlSet B C xy).Nonempty := by
    apply isCompact_stateControls.inter_iInter_nonempty
    · exact fun xy ↦ isClosed_additiveControlSet B C xy
    · intro s
      obtain ⟨z, hz, hzs⟩ := hfinite s
      refine ⟨z, hz, ?_⟩
      simp only [mem_iInter]
      intro xy hxy
      exact hzs xy hxy
  obtain ⟨z, hz, hall⟩ := hne
  refine ⟨z, hz, fun x y ↦ ?_⟩
  have hxy := (mem_iInter.mp hall) (x, y)
  exact sub_nonpos.mp hxy

/-- The real-variable AM--GM optimization used after additive domination.
It deliberately quantifies over every positive scale, including the cases
where one gauge or the constant vanishes. -/
theorem sq_le_sq_mul_of_scaled_additive
    {n C L R : ℝ} (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hscale : ∀ t : ℝ, 0 < t →
      t * n ≤ (C / 2) * (t ^ 2 * L + R)) :
    n ^ 2 ≤ C ^ 2 * L * R := by
  by_cases hnzero : n = 0
  · simp [hnzero, mul_nonneg (mul_nonneg (sq_nonneg C) hL) hR]
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hnzero)
  by_cases hCzero : C = 0
  · have h := hscale 1 zero_lt_one
    rw [hCzero] at h
    norm_num at h
    exact (not_lt_of_ge h hnpos).elim
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
  by_cases hLzero : L = 0
  · let t : ℝ := C * R / n + 1
    have hCR : 0 ≤ C * R := mul_nonneg hC hR
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have h := hscale t ht
    rw [hLzero] at h
    simp only [mul_zero, zero_add] at h
    have htprod : t * n = C * R + n := by
      dsimp [t]
      field_simp [hnzero]
      <;> ring
    rw [htprod] at h
    exfalso
    nlinarith
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
  have hCLpos : 0 < C * L := mul_pos hCpos hLpos
  let t : ℝ := n / (C * L)
  have ht : 0 < t := div_pos hnpos hCLpos
  have h := hscale t ht
  have hfactor : 0 ≤ 2 * C * L := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hfactor
  dsimp [t] at hmul
  field_simp [hCzero, hLzero] at hmul
  nlinarith

theorem leftSquare_real_smul (z : StateControl A D) (t : ℝ) (x : A) :
    leftSquare z ((t : ℂ) • x) = t ^ 2 * leftSquare z x := by
  simp [leftSquare, star_smul, pow_two, smul_mul_assoc, mul_smul_comm,
    mul_smul, weakDual_apply_real_smul, Complex.real_smul]
  ring

theorem rightSquare_real_smul (z : StateControl A D) (t : ℝ) (y : D) :
    rightSquare z ((t : ℂ) • y) = t ^ 2 * rightSquare z y := by
  simp [rightSquare, star_smul, pow_two, smul_mul_assoc, mul_smul_comm,
    mul_smul, weakDual_apply_real_smul, Complex.real_smul]
  ring

theorem leftSquare_complex_smul (z : StateControl A D) (c : ℂ) (x : A) :
    leftSquare z (c • x) = ‖c‖ ^ 2 * leftSquare z x := by
  simp [leftSquare, star_smul, smul_mul_assoc, mul_smul_comm, mul_smul,
    map_smul, ← Complex.normSq_eq_conj_mul_self,
    Complex.mul_re]
  rw [Complex.sq_norm]
  rw [Complex.normSq_apply]
  ring

theorem rightSquare_complex_smul (z : StateControl A D) (c : ℂ) (y : D) :
    rightSquare z (c • y) = ‖c‖ ^ 2 * rightSquare z y := by
  simp [rightSquare, star_smul, smul_mul_assoc, mul_smul_comm, mul_smul,
    map_smul, ← Complex.normSq_eq_conj_mul_self,
    Complex.mul_re]
  rw [Complex.sq_norm]
  rw [Complex.normSq_apply]
  ring

/-- The selected additive states satisfy the product estimate.  The same
states are retained throughout: scaling is applied to the input pair, not to
the selected quadruple. -/
theorem exists_global_productControl_of_weighted
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    ∃ z ∈ stateControls (A := A) (D := D),
      ∀ x y, ‖B x y‖ ^ 2 ≤
        C ^ 2 * leftSquare z x * rightSquare z y := by
  obtain ⟨z, hz, hadd⟩ :=
    exists_global_additiveControl_of_weighted B C hweighted
  refine ⟨z, hz, fun x y ↦ ?_⟩
  apply sq_le_sq_mul_of_scaled_additive
    (norm_nonneg (B x y)) hC
    (leftSquare_nonneg hz x) (rightSquare_nonneg hz y)
  intro t ht
  have h := hadd ((t : ℂ) • x) y
  rw [leftSquare_real_smul] at h
  have hnorm : ‖B ((t : ℂ) • x) y‖ = t * ‖B x y‖ := by
    calc
      ‖B ((t : ℂ) • x) y‖ = ‖(t : ℂ) • B x y‖ := by
        congr 1
        simp
      _ = t * ‖B x y‖ := by
        simp [norm_smul, abs_of_pos ht]
  rw [hnorm] at h
  exact h

/-- The weighted additive estimate supplies exactly the finite product
premise consumed by `StateSelection.lean`, with one quadruple for every
member of the finite set. -/
theorem finite_stateControl_of_weightedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    ∀ s : Finset (A × D),
      ∃ z ∈ stateControls (A := A) (D := D),
        ∀ xy ∈ s, z ∈ controlSet B C xy := by
  obtain ⟨z, hz, hall⟩ :=
    exists_global_productControl_of_weighted B C hC hweighted
  intro s
  refine ⟨z, hz, fun xy _ ↦ ?_⟩
  exact hall xy.1 xy.2

theorem exists_twoSidedDomination_of_weightedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    ∃ (p q : A →ₚ[ℂ] ℂ) (r t : D →ₚ[ℂ] ℂ),
      IsTwoSidedDominated B p q r t C :=
  exists_twoSidedDomination_of_finite_stateControl B C hC
    (finite_stateControl_of_weightedAdditive B C hC hweighted)

theorem isWeaklyCompact_of_weightedAdditive
    [Nontrivial A] [Nontrivial D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hweighted : HasWeightedFiniteAdditiveEstimate B C) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B :=
  isWeaklyCompact_of_finite_stateControl B C hC
    (finite_stateControl_of_weightedAdditive B C hC hweighted)

/-- A zero bilinear operator is weakly compact without any state-space
nonemptiness assumption. -/
theorem isWeaklyCompact_zero :
    MathlibAnnex.WeakCompact.IsWeaklyCompact
      (0 : A →L[ℂ] D →L[ℂ] ℂ) := by
  have h := MathlibAnnex.WeakCompact.isWeaklyCompact_of_factorization
    (0 : A →L[ℂ] ℂ) (0 : ℂ →L[ℂ] StrongDual ℂ D)
    MathlibAnnex.WeakCompact.isReflexive_innerProductSpace
  simpa using h

theorem bilinear_eq_zero_of_subsingleton_left [Subsingleton A]
    (B : A →L[ℂ] D →L[ℂ] ℂ) : B = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : x = 0 := Subsingleton.elim x 0
  simp [hx]

theorem bilinear_eq_zero_of_subsingleton_right [Subsingleton D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) : B = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  have hy : y = 0 := Subsingleton.elim y 0
  simp [hy]

/-- The zero-algebra left branch bypasses normalized states entirely. -/
theorem isWeaklyCompact_of_subsingleton_left [Subsingleton A]
    (B : A →L[ℂ] D →L[ℂ] ℂ) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  rw [bilinear_eq_zero_of_subsingleton_left B]
  exact isWeaklyCompact_zero

/-- The zero-algebra right branch bypasses normalized states entirely. -/
theorem isWeaklyCompact_of_subsingleton_right [Subsingleton D]
    (B : A →L[ℂ] D →L[ℂ] ℂ) :
    MathlibAnnex.WeakCompact.IsWeaklyCompact B := by
  rw [bilinear_eq_zero_of_subsingleton_right B]
  exact isWeaklyCompact_zero

end

end MathlibAnnex.CStarBilinear
