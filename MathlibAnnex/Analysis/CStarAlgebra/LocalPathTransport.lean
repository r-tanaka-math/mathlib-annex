import MathlibAnnex.Analysis.CStarAlgebra.AsymptoticallyInner
import MathlibAnnex.Analysis.CStarAlgebra.DenseCauchy
import MathlibAnnex.Topology.InfinitePath
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Finite path transport data

This file isolates the project-independent local input used by alternating
state-transport arguments.  The protected quantifier order is part of the
structure: the control set and tolerance are chosen before the comparison
functional and before its later approximation request.
-/

set_option autoImplicit false

noncomputable section

open Filter TopologicalSpace

namespace MathlibAnnex.CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- The convention used by path transport: `innerAt u = Ad(u*)`. -/
noncomputable def innerAt (u : unitary A) : A ≃⋆ₐ[ℂ] A :=
  Unitary.conjStarAlgAut ℂ A (star u)

/-- A C-star automorphism as a continuous linear isometry. -/
noncomputable def automorphismContinuousLinearMap (alpha : A ≃⋆ₐ[ℂ] A) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := alpha
      map_add' := map_add alpha
      map_smul' := map_smul alpha } 1 fun a => by
    change ‖alpha a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact le_of_eq (by
      simpa only [dist_zero_right, map_zero] using
        (StarAlgEquiv.isometry alpha).dist_eq a 0)

@[simp]
theorem automorphismContinuousLinearMap_apply (alpha : A ≃⋆ₐ[ℂ] A) (a : A) :
    automorphismContinuousLinearMap alpha a = alpha a :=
  rfl

/-- Pull a continuous functional back along `innerAt u`. -/
noncomputable def pull (phi : A →L[ℂ] ℂ) (u : unitary A) : A →L[ℂ] ℂ :=
  phi.comp (automorphismContinuousLinearMap (innerAt u))

@[simp]
theorem pull_apply (phi : A →L[ℂ] ℂ) (u : unitary A) (a : A) :
    pull phi u a = phi (innerAt u a) :=
  rfl

@[simp]
theorem pull_one (phi : A →L[ℂ] ℂ) : pull phi 1 = phi := by
  ext a
  simp [pull, innerAt]

theorem pull_mul (phi : A →L[ℂ] ℂ) (u v : unitary A) :
    pull phi (u * v) = pull (pull phi v) u := by
  ext a
  simp [pull, innerAt, mul_assoc]

/-- Uniform forward and inverse centrality along a path from the identity. -/
def PathCentralOn {u : unitary A} (p : Path (1 : unitary A) u) (F : Finset A)
    (epsilon : ℝ) : Prop :=
  ∀ t, ∀ a ∈ F,
    ‖(p t : A) * a * star (p t : A) - a‖ < epsilon ∧
      ‖star (p t : A) * a * (p t : A) - a‖ < epsilon

/-- A norm-at-most-one family which is closed under inner pullback. -/
structure InnerInvariantFamily (S : Set (A →L[ℂ] ℂ)) : Prop where
  norm_le_one : ∀ phi ∈ S, ‖phi‖ ≤ 1
  pull_mem : ∀ phi ∈ S, ∀ u : unitary A, pull phi u ∈ S

/-- Finite local path input for an alternating transport construction.

`protected` deliberately chooses `G, delta` before `psi`, and its returned
movement can subsequently be asked to handle any `H, eta`.  This prevents a
later test set from being chosen after the hypothesis meant to control it.
-/
structure FinitePathTransport (S : Set (A →L[ℂ] ℂ)) extends
    InnerInvariantFamily S : Prop where
  approximate : ∀ phi ∈ S, ∀ psi ∈ S, ∀ F : Finset A, ∀ epsilon : ℝ,
    0 < epsilon →
      ∃ u : unitary A, ∃ p : Path 1 u,
        ∀ a ∈ F, ‖pull phi u a - psi a‖ < epsilon
  protected_approximate : ∀ phi ∈ S, ∀ F : Finset A, ∀ epsilon : ℝ,
    0 < epsilon →
      ∃ G : Finset A, ∃ delta : ℝ, 0 < delta ∧
        ∀ psi ∈ S,
          (∀ a ∈ G, ‖phi a - psi a‖ < delta) →
          ∀ H : Finset A, ∀ eta : ℝ, 0 < eta →
            ∃ u : unitary A, ∃ p : Path 1 u,
              PathCentralOn p F epsilon ∧
                ∀ a ∈ H, ‖pull phi u a - psi a‖ < eta

/-- The unprotected approximation is symmetric after reversing the roles of
the two family members; this is a convenient orientation adapter. -/
theorem FinitePathTransport.approximate_rev {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S) (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) (F : Finset A) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ u : unitary A, ∃ p : Path 1 u,
      ∀ a ∈ F, ‖psi a - pull phi u a‖ < epsilon := by
  obtain ⟨u, p, hp⟩ := h.approximate phi hphi psi hpsi F epsilon hepsilon
  exact ⟨u, p, fun a ha => by simpa [norm_sub_rev] using hp a ha⟩

section Alternating

variable [TopologicalSpace.SeparableSpace A]

noncomputable def pathDense : ℕ → A := denseSeq A

theorem denseRange_pathDense : DenseRange (pathDense : ℕ → A) :=
  denseRange_denseSeq A

noncomputable def pathDensePrefix (n : ℕ) : Finset A :=
  by classical exact (Finset.range (n + 1)).image pathDense

noncomputable def pathProtectedPrefix (u : unitary A) (n : ℕ) : Finset A :=
  by classical exact pathDensePrefix n ∪
    (pathDensePrefix n).image (innerAt u).symm

def pathBudget (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem pathBudget_pos (n : ℕ) : 0 < pathBudget n := by
  norm_num [pathBudget]

theorem summable_pathBudget : Summable pathBudget := by
  change Summable fun n : ℕ => (1 / 2 : ℝ) ^ n
  exact summable_geometric_of_norm_lt_one (by norm_num)

theorem mem_pathDensePrefix {j n : ℕ} (hjn : j ≤ n) :
    pathDense j ∈ pathDensePrefix (A := A) n := by
  classical
  simp only [pathDensePrefix]
  exact Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjn), rfl⟩

theorem mem_pathProtectedPrefix {u : unitary A} {j n : ℕ} (hjn : j ≤ n) :
    pathDense j ∈ pathProtectedPrefix u n := by
  classical
  exact Finset.mem_union_left _ (mem_pathDensePrefix hjn)

theorem mem_symm_pathProtectedPrefix {u : unitary A} {j n : ℕ} (hjn : j ≤ n) :
    (innerAt u).symm (pathDense j) ∈ pathProtectedPrefix u n := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨pathDense j, mem_pathDensePrefix hjn, rfl⟩

/-- A recursion state whose left protected theorem has already consumed the
closeness to the current right functional. -/
structure PathAlternatingState {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) (step : ℕ) where
  left : unitary A
  right : unitary A
  leftPath : Path 1 left
  rightPath : Path 1 right
  left_mem : pull phi left ∈ S
  right_mem : pull psi right ∈ S
  move : ∀ (F' : Finset A) (epsilon' : ℝ), 0 < epsilon' →
    ∃ u : unitary A, ∃ p : Path 1 u,
      PathCentralOn p (pathProtectedPrefix left step) (pathBudget step) ∧
        ∀ a ∈ F', ‖pull (pull phi left) u a - pull psi right a‖ < epsilon'

/-- One alternating left/right correction. -/
structure PathAlternatingTransition {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) {step : ℕ}
    (s : PathAlternatingState h phi hphi psi hpsi step) where
  leftCorrection : unitary A
  rightCorrection : unitary A
  leftCorrectionPath : Path 1 leftCorrection
  rightCorrectionPath : Path 1 rightCorrection
  next : PathAlternatingState h phi hphi psi hpsi (step + 1)
  next_left : next.left = leftCorrection * s.left
  next_right : next.right = rightCorrection * s.right
  left_small : PathCentralOn leftCorrectionPath
    (pathProtectedPrefix s.left step) (pathBudget step)
  right_small : PathCentralOn rightCorrectionPath
    (pathProtectedPrefix s.right step) (pathBudget step)
  state_small : ∀ j, j ≤ step →
    ‖pull phi next.left ((innerAt s.right).symm (pathDense j)) -
      pull psi s.right ((innerAt s.right).symm (pathDense j))‖ < pathBudget step

set_option maxHeartbeats 1600000 in
theorem FinitePathTransport.nonempty_transition {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) {step : ℕ}
    (s : PathAlternatingState h phi hphi psi hpsi step) :
    Nonempty (PathAlternatingTransition h phi hphi psi hpsi s) := by
  classical
  obtain ⟨Gright, dright, hdright, hright⟩ :=
    h.protected_approximate (pull psi s.right) s.right_mem
      (pathProtectedPrefix s.right step) (pathBudget step) (pathBudget_pos step)
  let requestLeft : Finset A := Gright ∪
    (pathDensePrefix step).image (innerAt s.right).symm
  have hmin : 0 < min dright (pathBudget step) :=
    lt_min hdright (pathBudget_pos step)
  obtain ⟨u, pu, husmall, huapprox⟩ := s.move requestLeft _ hmin
  let left' : unitary A := u * s.left
  have hleftFun : pull phi left' = pull (pull phi s.left) u := by
    exact pull_mul phi u s.left
  have hleftMem : pull phi left' ∈ S := by
    rw [hleftFun]
    exact h.pull_mem _ s.left_mem u
  obtain ⟨Gleft, dleft, hdleft, hleft⟩ :=
    h.protected_approximate (pull phi left') hleftMem
      (pathProtectedPrefix left' (step + 1)) (pathBudget (step + 1))
      (pathBudget_pos (step + 1))
  have hrightClose : ∀ a ∈ Gright,
      ‖pull psi s.right a - pull phi left' a‖ < dright := by
    intro a ha
    have ha' : a ∈ requestLeft := Finset.mem_union_left _ ha
    have hh := huapprox a ha'
    rw [← hleftFun] at hh
    exact lt_of_lt_of_le (by simpa [norm_sub_rev] using hh) (min_le_left _ _)
  obtain ⟨v, pv, hvsmall, hvapprox⟩ :=
    hright (pull phi left') hleftMem hrightClose Gleft dleft hdleft
  let right' : unitary A := v * s.right
  have hrightFun : pull psi right' = pull (pull psi s.right) v := by
    exact pull_mul psi v s.right
  have hrightMem : pull psi right' ∈ S := by
    rw [hrightFun]
    exact h.pull_mem _ s.right_mem v
  have hleftClose : ∀ a ∈ Gleft,
      ‖pull phi left' a - pull psi right' a‖ < dleft := by
    intro a ha
    rw [hrightFun]
    simpa [norm_sub_rev] using hvapprox a ha
  let leftSegment : Path s.left left' :=
    { toFun := fun t => pu t * s.left
      continuous_toFun := by fun_prop
      source' := by rw [pu.source]; simp
      target' := by rw [pu.target] }
  let rightSegment : Path s.right right' :=
    { toFun := fun t => pv t * s.right
      continuous_toFun := by fun_prop
      source' := by rw [pv.source]; simp
      target' := by rw [pv.target] }
  let next : PathAlternatingState h phi hphi psi hpsi (step + 1) :=
    { left := left'
      right := right'
      leftPath := s.leftPath.trans leftSegment
      rightPath := s.rightPath.trans rightSegment
      left_mem := hleftMem
      right_mem := hrightMem
      move := hleft (pull psi right') hrightMem hleftClose }
  refine ⟨{
    leftCorrection := u
    rightCorrection := v
    leftCorrectionPath := pu
    rightCorrectionPath := pv
    next := next
    next_left := rfl
    next_right := rfl
    left_small := husmall
    right_small := hvsmall
    state_small := ?_ }⟩
  intro j hj
  have hh := huapprox ((innerAt s.right).symm (pathDense j))
    (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨pathDense j, mem_pathDensePrefix hj, rfl⟩))
  rw [← hleftFun] at hh
  exact lt_of_lt_of_le hh (min_le_right _ _)

set_option maxHeartbeats 1600000 in
theorem FinitePathTransport.nonempty_initialState {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) :
    Nonempty (PathAlternatingState h phi hphi psi hpsi 0) := by
  classical
  obtain ⟨Gright, dright, hdright, hright⟩ :=
    h.protected_approximate psi hpsi (pathProtectedPrefix 1 0)
      (pathBudget 0) (pathBudget_pos 0)
  obtain ⟨u, pu, huapprox⟩ :=
    h.approximate phi hphi psi hpsi Gright dright hdright
  let left' : unitary A := u
  have hleftMem : pull phi left' ∈ S := h.pull_mem phi hphi u
  obtain ⟨Gleft, dleft, hdleft, hleft⟩ :=
    h.protected_approximate (pull phi left') hleftMem
      (pathProtectedPrefix left' 0) (pathBudget 0) (pathBudget_pos 0)
  have hrightClose : ∀ a ∈ Gright, ‖psi a - pull phi left' a‖ < dright := by
    intro a ha
    simpa [norm_sub_rev] using huapprox a ha
  obtain ⟨v, pv, _hvsmall, hvapprox⟩ :=
    hright (pull phi left') hleftMem hrightClose Gleft dleft hdleft
  let right' : unitary A := v
  have hrightMem : pull psi right' ∈ S := h.pull_mem psi hpsi v
  have hleftClose : ∀ a ∈ Gleft,
      ‖pull phi left' a - pull psi right' a‖ < dleft := by
    intro a ha
    simpa [norm_sub_rev] using hvapprox a ha
  exact ⟨{
    left := left'
    right := right'
    leftPath := pu
    rightPath := pv
    left_mem := hleftMem
    right_mem := hrightMem
    move := hleft (pull psi right') hrightMem hleftClose }⟩

noncomputable def FinitePathTransport.initialState {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) :
    PathAlternatingState h phi hphi psi hpsi 0 :=
  Classical.choice (h.nonempty_initialState phi hphi psi hpsi)

noncomputable def FinitePathTransport.chosenTransition {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) {step : ℕ}
    (s : PathAlternatingState h phi hphi psi hpsi step) :
    PathAlternatingTransition h phi hphi psi hpsi s :=
  Classical.choice (h.nonempty_transition phi hphi psi hpsi s)

noncomputable def FinitePathTransport.states {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) :
    (n : ℕ) → PathAlternatingState h phi hphi psi hpsi n
  | 0 => h.initialState phi hphi psi hpsi
  | n + 1 => (h.chosenTransition phi hphi psi hpsi
      (h.states phi hphi psi hpsi n)).next

noncomputable def FinitePathTransport.transitions {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) (n : ℕ) :
    PathAlternatingTransition h phi hphi psi hpsi
      (h.states phi hphi psi hpsi n) :=
  h.chosenTransition phi hphi psi hpsi (h.states phi hphi psi hpsi n)

section Paths

variable {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S)

local notation "Q" => h.states phi hphi psi hpsi
local notation "R" => h.transitions phi hphi psi hpsi

/-- Integer-time vertices of the left concatenated path. -/
noncomputable def leftPathPoints : ℤ → unitary A
  | .ofNat 0 => 1
  | .ofNat (n + 1) => (Q n).left
  | .negSucc _ => 1

/-- Integer-time vertices of the right concatenated path. -/
noncomputable def rightPathPoints : ℤ → unitary A
  | .ofNat 0 => 1
  | .ofNat (n + 1) => (Q n).right
  | .negSucc _ => 1

/-- Translate a correction path on the right by the accumulated unitary. -/
def translatedCorrectionPath {u w : unitary A} (p : Path 1 u) :
    Path w (u * w) :=
  { toFun := fun t => p t * w
    continuous_toFun := by fun_prop
    source' := by rw [p.source]; simp
    target' := by rw [p.target] }

noncomputable def leftPathSegments :
    (z : ℤ) → Path
      (leftPathPoints h phi hphi psi hpsi z)
      (leftPathPoints h phi hphi psi hpsi (z + 1))
  | .ofNat 0 => (Q 0).leftPath
  | .ofNat (n + 1) => by
      let q : Path (Q n).left ((R n).leftCorrection * (Q n).left) :=
        translatedCorrectionPath (w := (Q n).left) (R n).leftCorrectionPath
      exact q.cast (by simp [leftPathPoints]) (by
        simp only [leftPathPoints]
        change (Q (n + 1)).left = (R n).leftCorrection * (Q n).left
        exact (R n).next_left)
  | .negSucc n => by
      have hz : Int.negSucc n + 1 =
          match n with
          | 0 => (0 : ℤ)
          | k + 1 => Int.negSucc k := by
        cases n <;> simp [Int.negSucc_eq]
      rw [hz]
      cases n <;> exact Path.refl _

noncomputable def rightPathSegments :
    (z : ℤ) → Path
      (rightPathPoints h phi hphi psi hpsi z)
      (rightPathPoints h phi hphi psi hpsi (z + 1))
  | .ofNat 0 => (Q 0).rightPath
  | .ofNat (n + 1) => by
      let q : Path (Q n).right ((R n).rightCorrection * (Q n).right) :=
        translatedCorrectionPath (w := (Q n).right) (R n).rightCorrectionPath
      exact q.cast (by simp [rightPathPoints]) (by
        simp only [rightPathPoints]
        change (Q (n + 1)).right = (R n).rightCorrection * (Q n).right
        exact (R n).next_right)
  | .negSucc n => by
      have hz : Int.negSucc n + 1 =
          match n with
          | 0 => (0 : ℤ)
          | k + 1 => Int.negSucc k := by
        cases n <;> simp [Int.negSucc_eq]
      rw [hz]
      cases n <;> exact Path.refl _

noncomputable def leftContinuousPath (t : ℝ) : unitary A :=
  MathlibAnnex.Path.infiniteConcat
    (leftPathPoints h phi hphi psi hpsi)
    (leftPathSegments h phi hphi psi hpsi) t

noncomputable def rightContinuousPath (t : ℝ) : unitary A :=
  MathlibAnnex.Path.infiniteConcat
    (rightPathPoints h phi hphi psi hpsi)
    (rightPathSegments h phi hphi psi hpsi) t

theorem continuous_leftContinuousPath :
    Continuous (leftContinuousPath h phi hphi psi hpsi) :=
  MathlibAnnex.Path.continuous_infiniteConcat _ _

theorem continuous_rightContinuousPath :
    Continuous (rightContinuousPath h phi hphi psi hpsi) :=
  MathlibAnnex.Path.continuous_infiniteConcat _ _

theorem leftContinuousPath_zero :
    leftContinuousPath h phi hphi psi hpsi 0 = 1 := by
  rw [leftContinuousPath, MathlibAnnex.Path.infiniteConcat, Int.floor_zero]
  change (Q 0).leftPath
    ⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ = 1
  rw [show (⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ :
      unitInterval) = 0 by ext; norm_num [Int.fract]]
  exact (Q 0).leftPath.source

theorem rightContinuousPath_zero :
    rightContinuousPath h phi hphi psi hpsi 0 = 1 := by
  rw [rightContinuousPath, MathlibAnnex.Path.infiniteConcat, Int.floor_zero]
  change (Q 0).rightPath
    ⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ = 1
  rw [show (⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ :
      unitInterval) = 0 by ext; norm_num [Int.fract]]
  exact (Q 0).rightPath.source

theorem leftContinuousPath_segment (n : ℕ)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    leftContinuousPath h phi hphi psi hpsi t =
      (R n).leftCorrectionPath
          ⟨(t : ℝ) - (n + 1), by
            constructor
            · exact sub_nonneg.mpr (by simpa using t.property.1)
            · apply (sub_le_iff_le_add).mpr
              linarith [t.property.2]⟩ *
        (Q n).left := by
  let tz : Set.Icc ((Int.ofNat (n + 1) : ℤ) : ℝ)
      ((Int.ofNat (n + 1) : ℤ) + 1 : ℝ) :=
    ⟨t, by
      constructor
      · simpa using t.property.1
      · have ht := t.property.2
        norm_num at ht ⊢
        linarith⟩
  have hh := MathlibAnnex.Path.infiniteConcat_eq_intervalPath
    (leftPathPoints h phi hphi psi hpsi)
    (leftPathSegments h phi hphi psi hpsi)
    (Int.ofNat (n + 1)) tz
  dsimp only [tz] at hh
  convert hh using 1 <;>
    simp [leftContinuousPath, MathlibAnnex.Path.intervalPath,
      leftPathSegments, translatedCorrectionPath, Path.cast]
  congr 2

theorem rightContinuousPath_segment (n : ℕ)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    rightContinuousPath h phi hphi psi hpsi t =
      (R n).rightCorrectionPath
          ⟨(t : ℝ) - (n + 1), by
            constructor
            · exact sub_nonneg.mpr (by simpa using t.property.1)
            · apply (sub_le_iff_le_add).mpr
              linarith [t.property.2]⟩ *
        (Q n).right := by
  let tz : Set.Icc ((Int.ofNat (n + 1) : ℤ) : ℝ)
      ((Int.ofNat (n + 1) : ℤ) + 1 : ℝ) :=
    ⟨t, by
      constructor
      · simpa using t.property.1
      · have ht := t.property.2
        norm_num at ht ⊢
        linarith⟩
  have hh := MathlibAnnex.Path.infiniteConcat_eq_intervalPath
    (rightPathPoints h phi hphi psi hpsi)
    (rightPathSegments h phi hphi psi hpsi)
    (Int.ofNat (n + 1)) tz
  dsimp only [tz] at hh
  convert hh using 1 <;>
    simp [rightContinuousPath, MathlibAnnex.Path.intervalPath,
      rightPathSegments, translatedCorrectionPath, Path.cast]
  congr 2

noncomputable def leftAutomorphisms (n : ℕ) : A ≃⋆ₐ[ℂ] A :=
  innerAt (Q n).left

noncomputable def rightAutomorphisms (n : ℕ) : A ≃⋆ₐ[ℂ] A :=
  innerAt (Q n).right

theorem leftAutomorphisms_step (n j : ℕ) (hj : j ≤ n) :
    ‖leftAutomorphisms h phi hphi psi hpsi (n + 1) (pathDense j) -
      leftAutomorphisms h phi hphi psi hpsi n (pathDense j)‖ ≤ pathBudget n := by
  let t := R n
  have hnext : Q (n + 1) = t.next := rfl
  rw [leftAutomorphisms, leftAutomorphisms, hnext, t.next_left]
  have hformula :
      innerAt (t.leftCorrection * (Q n).left) (pathDense j) =
        innerAt (Q n).left
          (star (t.leftCorrection : A) * pathDense j * (t.leftCorrection : A)) := by
    simp [innerAt, mul_assoc]
  rw [hformula]
  calc
    _ = ‖star (t.leftCorrection : A) * pathDense j *
          (t.leftCorrection : A) - pathDense j‖ := by
      have hh := (StarAlgEquiv.isometry (innerAt (Q n).left)).dist_eq
        (star (t.leftCorrection : A) * pathDense j * (t.leftCorrection : A))
        (pathDense j)
      simpa only [dist_eq_norm] using hh
    _ ≤ pathBudget n := by
      have hh := (t.left_small (1 : Set.Icc (0 : ℝ) 1) _
        (mem_pathProtectedPrefix hj)).2
      simpa only [t.leftCorrectionPath.target] using le_of_lt hh

theorem leftAutomorphisms_symm_step (n j : ℕ) (hj : j ≤ n) :
    ‖(leftAutomorphisms h phi hphi psi hpsi (n + 1)).symm (pathDense j) -
      (leftAutomorphisms h phi hphi psi hpsi n).symm (pathDense j)‖ ≤
        pathBudget n := by
  let t := R n
  have hnext : Q (n + 1) = t.next := rfl
  rw [leftAutomorphisms, leftAutomorphisms, hnext, t.next_left]
  have hformula :
      (innerAt (t.leftCorrection * (Q n).left)).symm (pathDense j) =
        (t.leftCorrection : A) * (innerAt (Q n).left).symm (pathDense j) *
          star (t.leftCorrection : A) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change ((t.leftCorrection : A) * (Q n).left) * pathDense j *
        star ((t.leftCorrection : A) * (Q n).left) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula]
  have hh := (t.left_small (1 : Set.Icc (0 : ℝ) 1) _
    (mem_symm_pathProtectedPrefix hj)).1
  simpa only [t.leftCorrectionPath.target] using le_of_lt hh

theorem rightAutomorphisms_step (n j : ℕ) (hj : j ≤ n) :
    ‖rightAutomorphisms h phi hphi psi hpsi (n + 1) (pathDense j) -
      rightAutomorphisms h phi hphi psi hpsi n (pathDense j)‖ ≤ pathBudget n := by
  let t := R n
  have hnext : Q (n + 1) = t.next := rfl
  rw [rightAutomorphisms, rightAutomorphisms, hnext, t.next_right]
  have hformula :
      innerAt (t.rightCorrection * (Q n).right) (pathDense j) =
        innerAt (Q n).right
          (star (t.rightCorrection : A) * pathDense j * (t.rightCorrection : A)) := by
    simp [innerAt, mul_assoc]
  rw [hformula]
  calc
    _ = ‖star (t.rightCorrection : A) * pathDense j *
          (t.rightCorrection : A) - pathDense j‖ := by
      have hh := (StarAlgEquiv.isometry (innerAt (Q n).right)).dist_eq
        (star (t.rightCorrection : A) * pathDense j * (t.rightCorrection : A))
        (pathDense j)
      simpa only [dist_eq_norm] using hh
    _ ≤ pathBudget n := by
      have hh := (t.right_small (1 : Set.Icc (0 : ℝ) 1) _
        (mem_pathProtectedPrefix hj)).2
      simpa only [t.rightCorrectionPath.target] using le_of_lt hh

theorem rightAutomorphisms_symm_step (n j : ℕ) (hj : j ≤ n) :
    ‖(rightAutomorphisms h phi hphi psi hpsi (n + 1)).symm (pathDense j) -
      (rightAutomorphisms h phi hphi psi hpsi n).symm (pathDense j)‖ ≤
        pathBudget n := by
  let t := R n
  have hnext : Q (n + 1) = t.next := rfl
  rw [rightAutomorphisms, rightAutomorphisms, hnext, t.next_right]
  have hformula :
      (innerAt (t.rightCorrection * (Q n).right)).symm (pathDense j) =
        (t.rightCorrection : A) * (innerAt (Q n).right).symm (pathDense j) *
          star (t.rightCorrection : A) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change ((t.rightCorrection : A) * (Q n).right) * pathDense j *
        star ((t.rightCorrection : A) * (Q n).right) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula]
  have hh := (t.right_small (1 : Set.Icc (0 : ℝ) 1) _
    (mem_symm_pathProtectedPrefix hj)).1
  simpa only [t.rightCorrectionPath.target] using le_of_lt hh

theorem leftAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n => leftAutomorphisms h phi hphi psi hpsi n a) :=
  cauchySeq_of_summable_dense_steps pathDense denseRange_pathDense
    (leftAutomorphisms h phi hphi psi hpsi) pathBudget summable_pathBudget
    (leftAutomorphisms_step h phi hphi psi hpsi)

theorem leftAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (leftAutomorphisms h phi hphi psi hpsi n).symm a) :=
  cauchySeq_of_summable_dense_steps pathDense denseRange_pathDense
    (fun n => (leftAutomorphisms h phi hphi psi hpsi n).symm)
    pathBudget summable_pathBudget
    (leftAutomorphisms_symm_step h phi hphi psi hpsi)

theorem rightAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n => rightAutomorphisms h phi hphi psi hpsi n a) :=
  cauchySeq_of_summable_dense_steps pathDense denseRange_pathDense
    (rightAutomorphisms h phi hphi psi hpsi) pathBudget summable_pathBudget
    (rightAutomorphisms_step h phi hphi psi hpsi)

theorem rightAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (rightAutomorphisms h phi hphi psi hpsi n).symm a) :=
  cauchySeq_of_summable_dense_steps pathDense denseRange_pathDense
    (fun n => (rightAutomorphisms h phi hphi psi hpsi n).symm)
    pathBudget summable_pathBudget
    (rightAutomorphisms_symm_step h phi hphi psi hpsi)

theorem tendsto_pathBudget_zero : Tendsto pathBudget atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

noncomputable def leftLimitAutomorphism : A ≃⋆ₐ[ℂ] A :=
  twoSidedPointwiseLimit (leftAutomorphisms h phi hphi psi hpsi)
    (leftAutomorphisms_cauchy h phi hphi psi hpsi)
    (leftAutomorphisms_symm_cauchy h phi hphi psi hpsi)

noncomputable def rightLimitAutomorphism : A ≃⋆ₐ[ℂ] A :=
  twoSidedPointwiseLimit (rightAutomorphisms h phi hphi psi hpsi)
    (rightAutomorphisms_cauchy h phi hphi psi hpsi)
    (rightAutomorphisms_symm_cauchy h phi hphi psi hpsi)

theorem leftContinuousPath_forward_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖innerAt (leftContinuousPath h phi hphi psi hpsi t) (pathDense j) -
      leftAutomorphisms h phi hphi psi hpsi n (pathDense j)‖ ≤ pathBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [leftContinuousPath_segment h phi hphi psi hpsi n t]
  have hformula :
      innerAt ((R n).leftCorrectionPath s * (Q n).left) (pathDense j) =
        innerAt (Q n).left
          (star ((R n).leftCorrectionPath s : A) * pathDense j *
            ((R n).leftCorrectionPath s : A)) := by
    simp [innerAt, mul_assoc]
  rw [hformula, leftAutomorphisms]
  calc
    _ = ‖star ((R n).leftCorrectionPath s : A) * pathDense j *
          ((R n).leftCorrectionPath s : A) - pathDense j‖ := by
      have hh := (StarAlgEquiv.isometry (innerAt (Q n).left)).dist_eq
        (star ((R n).leftCorrectionPath s : A) * pathDense j *
          ((R n).leftCorrectionPath s : A)) (pathDense j)
      simpa only [dist_eq_norm] using hh
    _ ≤ pathBudget n :=
      le_of_lt (((R n).left_small s _ (mem_pathProtectedPrefix hj)).2)

theorem rightContinuousPath_forward_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖innerAt (rightContinuousPath h phi hphi psi hpsi t) (pathDense j) -
      rightAutomorphisms h phi hphi psi hpsi n (pathDense j)‖ ≤ pathBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [rightContinuousPath_segment h phi hphi psi hpsi n t]
  have hformula :
      innerAt ((R n).rightCorrectionPath s * (Q n).right) (pathDense j) =
        innerAt (Q n).right
          (star ((R n).rightCorrectionPath s : A) * pathDense j *
            ((R n).rightCorrectionPath s : A)) := by
    simp [innerAt, mul_assoc]
  rw [hformula, rightAutomorphisms]
  calc
    _ = ‖star ((R n).rightCorrectionPath s : A) * pathDense j *
          ((R n).rightCorrectionPath s : A) - pathDense j‖ := by
      have hh := (StarAlgEquiv.isometry (innerAt (Q n).right)).dist_eq
        (star ((R n).rightCorrectionPath s : A) * pathDense j *
          ((R n).rightCorrectionPath s : A)) (pathDense j)
      simpa only [dist_eq_norm] using hh
    _ ≤ pathBudget n :=
      le_of_lt (((R n).right_small s _ (mem_pathProtectedPrefix hj)).2)

theorem tendsto_leftContinuousPath_forward (a : A) :
    Tendsto (fun t : ℝ => innerAt (leftContinuousPath h phi hphi psi hpsi t) a)
      atTop (nhds (leftLimitAutomorphism h phi hphi psi hpsi a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    pathDense denseRange_pathDense
    (fun n a => leftAutomorphisms h phi hphi psi hpsi n a)
    (fun t => innerAt (leftContinuousPath h phi hphi psi hpsi t))
    (fun n => StarAlgEquiv.isometry (leftAutomorphisms h phi hphi psi hpsi n))
    (fun t => StarAlgEquiv.isometry (innerAt
      (leftContinuousPath h phi hphi psi hpsi t)))
    pathBudget tendsto_pathBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        leftContinuousPath_forward_dense_segment h phi hphi psi hpsi n j hj t)
    a _
  simpa [leftLimitAutomorphism, twoSidedPointwiseLimit_apply,
    pointwiseLimitHom_apply] using
    tendsto_pointwiseLimit (leftAutomorphisms h phi hphi psi hpsi)
      (leftAutomorphisms_cauchy h phi hphi psi hpsi) a

theorem tendsto_rightContinuousPath_forward (a : A) :
    Tendsto (fun t : ℝ => innerAt (rightContinuousPath h phi hphi psi hpsi t) a)
      atTop (nhds (rightLimitAutomorphism h phi hphi psi hpsi a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    pathDense denseRange_pathDense
    (fun n a => rightAutomorphisms h phi hphi psi hpsi n a)
    (fun t => innerAt (rightContinuousPath h phi hphi psi hpsi t))
    (fun n => StarAlgEquiv.isometry (rightAutomorphisms h phi hphi psi hpsi n))
    (fun t => StarAlgEquiv.isometry (innerAt
      (rightContinuousPath h phi hphi psi hpsi t)))
    pathBudget tendsto_pathBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        rightContinuousPath_forward_dense_segment h phi hphi psi hpsi n j hj t)
    a _
  simpa [rightLimitAutomorphism, twoSidedPointwiseLimit_apply,
    pointwiseLimitHom_apply] using
    tendsto_pointwiseLimit (rightAutomorphisms h phi hphi psi hpsi)
      (rightAutomorphisms_cauchy h phi hphi psi hpsi) a

noncomputable def outputUnitary (n : ℕ) : unitary A :=
  star (Q (n + 1)).left * (Q n).right

noncomputable def outputAutomorphisms (n : ℕ) : A ≃⋆ₐ[ℂ] A :=
  Unitary.conjStarAlgAut ℂ A (outputUnitary h phi hphi psi hpsi n)

theorem outputAutomorphisms_eq (n : ℕ) :
    outputAutomorphisms h phi hphi psi hpsi n =
      (rightAutomorphisms h phi hphi psi hpsi n).symm.trans
        (leftAutomorphisms h phi hphi psi hpsi (n + 1)) := by
  ext a
  simp [outputAutomorphisms, outputUnitary, rightAutomorphisms,
    leftAutomorphisms, innerAt, mul_assoc]

theorem leftAutomorphisms_succ_cauchy :
    ∀ a, CauchySeq (fun n =>
      leftAutomorphisms h phi hphi psi hpsi (n + 1) a) := by
  intro a
  exact (cauchySeq_shift 1).2 (leftAutomorphisms_cauchy h phi hphi psi hpsi a)

theorem leftAutomorphisms_succ_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (leftAutomorphisms h phi hphi psi hpsi (n + 1)).symm a) := by
  intro a
  exact (cauchySeq_shift 1).2
    (leftAutomorphisms_symm_cauchy h phi hphi psi hpsi a)

theorem outputAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n => outputAutomorphisms h phi hphi psi hpsi n a) := by
  intro a
  have hh := cauchySeq_trans_of_isometry
    (fun n => leftAutomorphisms h phi hphi psi hpsi (n + 1))
    (fun n => (rightAutomorphisms h phi hphi psi hpsi n).symm)
    (leftAutomorphisms_succ_cauchy h phi hphi psi hpsi)
    (rightAutomorphisms_symm_cauchy h phi hphi psi hpsi) a
  simpa only [outputAutomorphisms_eq] using hh

theorem outputAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (outputAutomorphisms h phi hphi psi hpsi n).symm a) := by
  intro a
  have hh := cauchySeq_trans_of_isometry
    (rightAutomorphisms h phi hphi psi hpsi)
    (fun n => (leftAutomorphisms h phi hphi psi hpsi (n + 1)).symm)
    (rightAutomorphisms_cauchy h phi hphi psi hpsi)
    (leftAutomorphisms_succ_symm_cauchy h phi hphi psi hpsi) a
  have heq : ∀ n,
      (outputAutomorphisms h phi hphi psi hpsi n).symm =
        (leftAutomorphisms h phi hphi psi hpsi (n + 1)).symm.trans
          (rightAutomorphisms h phi hphi psi hpsi n) := by
    intro n
    rw [outputAutomorphisms_eq]
    rfl
  simpa only [heq] using hh

theorem outputAutomorphisms_state_dense (n j : ℕ) (hj : j ≤ n) :
    ‖phi (outputAutomorphisms h phi hphi psi hpsi n (pathDense j)) -
      psi (pathDense j)‖ < pathBudget n := by
  let t := R n
  have hnext : Q (n + 1) = t.next := rfl
  have hh := t.state_small j hj
  rw [← hnext] at hh
  have hleft :
      innerAt (Q (n + 1)).left
          ((innerAt (Q n).right).symm (pathDense j)) =
        outputAutomorphisms h phi hphi psi hpsi n (pathDense j) := by
    rw [outputAutomorphisms_eq]
    rfl
  simpa only [pull_apply, hleft,
    (innerAt (Q n).right).apply_symm_apply] using hh

theorem tendsto_outputAutomorphisms_state :
    ∀ a, Tendsto (fun n => phi (outputAutomorphisms h phi hphi psi hpsi n a))
      atTop (nhds (psi a)) := by
  have hphiNorm : ∀ a, ‖phi a‖ ≤ ‖a‖ := by
    intro a
    calc
      ‖phi a‖ ≤ ‖phi‖ * ‖a‖ := ContinuousLinearMap.le_opNorm phi a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (h.norm_le_one phi hphi) (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  have hpsiNorm : ∀ a, ‖psi a‖ ≤ ‖a‖ := by
    intro a
    calc
      ‖psi a‖ ≤ ‖psi‖ * ‖a‖ := ContinuousLinearMap.le_opNorm psi a
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (h.norm_le_one psi hpsi) (norm_nonneg a)
      _ = ‖a‖ := one_mul _
  apply tendsto_functional_of_dense_prefix pathDense denseRange_pathDense
    (outputAutomorphisms h phi hphi psi hpsi) phi psi hphiNorm hpsiNorm
    pathBudget tendsto_pathBudget_zero
  exact outputAutomorphisms_state_dense h phi hphi psi hpsi

/-- The equal-time limit of the two accumulated sides. -/
noncomputable def asymptoticAutomorphism : A ≃⋆ₐ[ℂ] A :=
  (rightLimitAutomorphism h phi hphi psi hpsi).symm.trans
    (leftLimitAutomorphism h phi hphi psi hpsi)

theorem tendsto_outputAutomorphisms_asymptoticAutomorphism (a : A) :
    Tendsto (fun n => outputAutomorphisms h phi hphi psi hpsi n a) atTop
      (nhds (asymptoticAutomorphism h phi hphi psi hpsi a)) := by
  have hright : Tendsto (fun n =>
      (rightAutomorphisms h phi hphi psi hpsi n).symm a) atTop
      (nhds ((rightLimitAutomorphism h phi hphi psi hpsi).symm a)) := by
    rw [rightLimitAutomorphism, twoSidedPointwiseLimit_symm_apply]
    exact tendsto_pointwiseLimit
      (fun n => (rightAutomorphisms h phi hphi psi hpsi n).symm)
      (rightAutomorphisms_symm_cauchy h phi hphi psi hpsi) a
  have hleft (b : A) : Tendsto (fun n =>
      leftAutomorphisms h phi hphi psi hpsi (n + 1) b) atTop
      (nhds (leftLimitAutomorphism h phi hphi psi hpsi b)) := by
    apply (tendsto_add_atTop_iff_nat
      (f := fun n => leftAutomorphisms h phi hphi psi hpsi n b) 1).2
    simpa [leftLimitAutomorphism, twoSidedPointwiseLimit_apply,
      pointwiseLimitHom_apply] using
      tendsto_pointwiseLimit (leftAutomorphisms h phi hphi psi hpsi)
        (leftAutomorphisms_cauchy h phi hphi psi hpsi) b
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun n => leftAutomorphisms h phi hphi psi hpsi (n + 1))
    (fun n => (rightAutomorphisms h phi hphi psi hpsi n).symm a)
    (fun n => StarAlgEquiv.isometry
      (leftAutomorphisms h phi hphi psi hpsi (n + 1)))
    hright (hleft ((rightLimitAutomorphism h phi hphi psi hpsi).symm a))
  simpa [outputAutomorphisms_eq, asymptoticAutomorphism] using hcomp

theorem asymptoticAutomorphism_state (a : A) :
    phi (asymptoticAutomorphism h phi hphi psi hpsi a) = psi a := by
  apply tendsto_nhds_unique
    ((phi.continuous.tendsto _).comp
      (tendsto_outputAutomorphisms_asymptoticAutomorphism
        h phi hphi psi hpsi a))
  exact tendsto_outputAutomorphisms_state h phi hphi psi hpsi a

/-- The single implementing path obtained from the two alternating sides. -/
noncomputable def implementingUnitary (t : ℝ) : unitary A :=
  star (leftContinuousPath h phi hphi psi hpsi t) *
    rightContinuousPath h phi hphi psi hpsi t

noncomputable def implementingAutomorphism (t : ℝ) : A ≃⋆ₐ[ℂ] A :=
  Unitary.conjStarAlgAut ℂ A (implementingUnitary h phi hphi psi hpsi t)

theorem continuous_implementingUnitary :
    Continuous (implementingUnitary h phi hphi psi hpsi) := by
  unfold implementingUnitary
  change Continuous (fun t =>
    (leftContinuousPath h phi hphi psi hpsi t)⁻¹ *
      rightContinuousPath h phi hphi psi hpsi t)
  exact (continuous_leftContinuousPath h phi hphi psi hpsi).inv.mul
    (continuous_rightContinuousPath h phi hphi psi hpsi)

theorem implementingUnitary_zero :
    implementingUnitary h phi hphi psi hpsi 0 = 1 := by
  simp [implementingUnitary,
    leftContinuousPath_zero h phi hphi psi hpsi,
    rightContinuousPath_zero h phi hphi psi hpsi]

theorem implementingAutomorphism_eq (t : ℝ) :
    implementingAutomorphism h phi hphi psi hpsi t =
      (innerAt (rightContinuousPath h phi hphi psi hpsi t)).symm.trans
        (innerAt (leftContinuousPath h phi hphi psi hpsi t)) := by
  ext a
  simp [implementingAutomorphism, implementingUnitary, innerAt, mul_assoc]

theorem tendsto_implementingAutomorphism (a : A) :
    Tendsto (fun t : ℝ => implementingAutomorphism h phi hphi psi hpsi t a)
      atTop (nhds (asymptoticAutomorphism h phi hphi psi hpsi a)) := by
  have hrightInv := tendsto_symm_apply_atTop_of_tendsto
    (fun t => innerAt (rightContinuousPath h phi hphi psi hpsi t))
    (rightLimitAutomorphism h phi hphi psi hpsi)
    (tendsto_rightContinuousPath_forward h phi hphi psi hpsi) a
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun t => innerAt (leftContinuousPath h phi hphi psi hpsi t))
    (fun t => (innerAt (rightContinuousPath h phi hphi psi hpsi t)).symm a)
    (fun t => StarAlgEquiv.isometry
      (innerAt (leftContinuousPath h phi hphi psi hpsi t)))
    hrightInv (tendsto_leftContinuousPath_forward h phi hphi psi hpsi
      ((rightLimitAutomorphism h phi hphi psi hpsi).symm a))
  simpa [implementingAutomorphism_eq, asymptoticAutomorphism] using hcomp

/-- Finite protected local path transport globalizes to a start-at-one
asymptotically inner automorphism with the exact functional equation. -/
theorem FinitePathTransport.exists_asymptoticallyInner
    {S : Set (A →L[ℂ] ℂ)} (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) :
    ∃ alpha : A ≃⋆ₐ[ℂ] A,
      IsAsymptoticallyInnerFromOne alpha ∧ ∀ a, phi (alpha a) = psi a := by
  refine ⟨asymptoticAutomorphism h phi hphi psi hpsi, ?_,
    asymptoticAutomorphism_state h phi hphi psi hpsi⟩
  exact ⟨implementingUnitary h phi hphi psi hpsi,
    continuous_implementingUnitary h phi hphi psi hpsi,
    implementingUnitary_zero h phi hphi psi hpsi,
    tendsto_implementingAutomorphism h phi hphi psi hpsi⟩

/-- The local finite supplier already yields a genuine automorphism with the
requested exact functional equation and a two-sided inner sequence. -/
theorem FinitePathTransport.exists_twoSidedLimit {S : Set (A →L[ℂ] ℂ)}
    (h : FinitePathTransport S)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ S)
    (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ S) :
    ∃ (alpha : A ≃⋆ₐ[ℂ] A) (f : ℕ → A ≃⋆ₐ[ℂ] A)
        (hf : ∀ a, CauchySeq (fun n => f n a))
        (hfinv : ∀ a, CauchySeq (fun n => (f n).symm a)),
      (∀ a, phi (alpha a) = psi a) ∧
        (∀ n, ∃ u : unitary A, f n = Unitary.conjStarAlgAut ℂ A u) ∧
        alpha = twoSidedPointwiseLimit f hf hfinv := by
  refine ⟨twoSidedPointwiseLimit (outputAutomorphisms h phi hphi psi hpsi)
      (outputAutomorphisms_cauchy h phi hphi psi hpsi)
      (outputAutomorphisms_symm_cauchy h phi hphi psi hpsi),
    outputAutomorphisms h phi hphi psi hpsi,
    outputAutomorphisms_cauchy h phi hphi psi hpsi,
    outputAutomorphisms_symm_cauchy h phi hphi psi hpsi,
    ?_, ?_, rfl⟩
  · exact (twoSidedPointwiseLimit_state_and_approximatelyInner
      (outputAutomorphisms h phi hphi psi hpsi)
      (outputAutomorphisms_cauchy h phi hphi psi hpsi)
      (outputAutomorphisms_symm_cauchy h phi hphi psi hpsi)
      (fun n => ⟨outputUnitary h phi hphi psi hpsi n, rfl⟩)
      phi psi (tendsto_outputAutomorphisms_state h phi hphi psi hpsi)).1
  · intro n
    exact ⟨outputUnitary h phi hphi psi hpsi n, rfl⟩

end Paths

end Alternating

end MathlibAnnex.CStarAlgebra
