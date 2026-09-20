import MathlibAnnex.Analysis.CStarAlgebra.DenseCauchy
import MathlibAnnex.Topology.InfinitePath
import Mathlib.Topology.Algebra.Star.Unitary
import MathlibAnnex.Analysis.CStarAlgebra.CAR.Homogeneity
import MathlibAnnex.Analysis.CStarAlgebra.CAR.StateTransport

/-!
# Alternating global transport for CAR pure states

The local test order is encoded in `AlternatingState`: its movement function
has already consumed the current stage-test closeness.  A transition first
moves the left vector close on the right tests, then moves the right vector
close on the next left tests.  Thus no future test set is chosen after the
hypothesis which has to control it.
-/

set_option autoImplicit false

noncomputable section

open Filter MathlibAnnex.Analysis.CStarAlgebra TopologicalSpace

namespace MathlibAnnex.CStarAlgebra.CAR

noncomputable def transportDense : ℕ → Limit := denseSeq Limit

theorem denseRange_transportDense : DenseRange transportDense :=
  denseRange_denseSeq Limit

noncomputable def densePrefix (n : ℕ) : Finset Limit :=
  by classical exact (Finset.range (n + 1)).image transportDense

noncomputable def innerAt (u : unitary Limit) : StarAlgEquiv ℂ Limit Limit :=
  Unitary.conjStarAlgAut ℂ Limit (star u)

noncomputable def protectedPrefix (u : unitary Limit) (n : ℕ) : Finset Limit :=
  by classical exact densePrefix n ∪ (densePrefix n).image (innerAt u).symm

noncomputable def stageTests (n : ℕ) : Finset Limit :=
  by
    classical
    exact (Finset.univ.product Finset.univ).image
      (fun ij : Fin (2 ^ n) × Fin (2 ^ n) => limitMatrixUnit n ij.1 ij.2)

def transportBudget (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem transportBudget_pos (n : ℕ) : 0 < transportBudget n := by
  norm_num [transportBudget]

theorem summable_transportBudget : Summable transportBudget := by
  change Summable fun n : ℕ => (1 / 2 : ℝ) ^ n
  exact summable_geometric_of_norm_lt_one (by norm_num)

theorem mem_densePrefix {j n : ℕ} (hjn : j ≤ n) :
    transportDense j ∈ densePrefix n := by
  classical
  simp only [densePrefix]
  apply Finset.mem_image.mpr
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjn), rfl⟩

theorem mem_protectedPrefix {u : unitary Limit} {j n : ℕ} (hjn : j ≤ n) :
    transportDense j ∈ protectedPrefix u n :=
  by
    classical
    exact Finset.mem_union_left _ (mem_densePrefix hjn)

theorem mem_symm_protectedPrefix {u : unitary Limit} {j n : ℕ} (hjn : j ≤ n) :
    (innerAt u).symm (transportDense j) ∈ protectedPrefix u n := by
  classical
  simp only [protectedPrefix]
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨transportDense j, mem_densePrefix hjn, rfl⟩

theorem mem_stageTests (n : ℕ) (i j : Fin (2 ^ n)) :
    limitMatrixUnit n i j ∈ stageTests n := by
  classical
  simp only [stageTests]
  apply Finset.mem_image.mpr
  exact ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

/-- A recursion state whose left local theorem has already been specialized
to the current right vector. -/
structure AlternatingState
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) (step : ℕ) where
  left : unitary Limit
  right : unitary Limit
  leftPath : Path 1 left
  rightPath : Path 1 right
  move : ∀ (F' : Finset Limit) (epsilon' : ℝ), 0 < epsilon' →
    ∃ u : unitary Limit,
      ∃ p : Path 1 u,
      (∀ t, ∀ a ∈ protectedPrefix left step,
        ‖(p t : Limit) * a * star (p t : Limit) - a‖ < transportBudget step ∧
        ‖star (p t : Limit) * a * (p t : Limit) - a‖ < transportBudget step) ∧
      ∀ a ∈ F',
        ‖Representation.vectorFunctional rho
              (rho (u : Limit) (rho (left : Limit) xi)) a -
          Representation.vectorFunctional sigma (sigma (right : Limit) eta) a‖ < epsilon'

/-- A transition records both small corrections and the state estimate at
the left midpoint, before the right correction is applied. -/
structure AlternatingTransition
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (sigma : Representation Limit K)
    (xi : H) (eta : K) {step : ℕ}
    (s : AlternatingState rho sigma xi eta step) where
  leftCorrection : unitary Limit
  rightCorrection : unitary Limit
  leftCorrectionPath : Path 1 leftCorrection
  rightCorrectionPath : Path 1 rightCorrection
  next : AlternatingState rho sigma xi eta (step + 1)
  next_left : next.left = leftCorrection * s.left
  next_right : next.right = rightCorrection * s.right
  left_small : ∀ t, ∀ a ∈ protectedPrefix s.left step,
    ‖( leftCorrectionPath t : Limit) * a * star (leftCorrectionPath t : Limit) - a‖ <
        transportBudget step ∧
    ‖star (leftCorrectionPath t : Limit) * a * (leftCorrectionPath t : Limit) - a‖ <
        transportBudget step
  right_small : ∀ t, ∀ a ∈ protectedPrefix s.right step,
    ‖( rightCorrectionPath t : Limit) * a * star (rightCorrectionPath t : Limit) - a‖ <
        transportBudget step ∧
    ‖star (rightCorrectionPath t : Limit) * a * (rightCorrectionPath t : Limit) - a‖ <
        transportBudget step
  state_small : ∀ j, j ≤ step →
    ‖Representation.vectorFunctional rho
          (rho (next.left : Limit) xi) ((innerAt s.right).symm (transportDense j)) -
      Representation.vectorFunctional sigma
          (sigma (s.right : Limit) eta) ((innerAt s.right).symm (transportDense j))‖ <
        transportBudget step

set_option maxHeartbeats 1600000 in
theorem nonempty_transition
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    {step : ℕ} (s : AlternatingState rho sigma xi eta step) :
    Nonempty (AlternatingTransition rho sigma xi eta s) := by
  classical
  have hleftUnit : ‖rho (s.left : Limit) xi‖ = 1 := by
    rw [(rho (s.left : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem rho s.left.property), hxi]
  have hrightUnit : ‖sigma (s.right : Limit) eta‖ = 1 := by
    rw [(sigma (s.right : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem sigma s.right.property), heta]
  obtain ⟨nb, db, hdb, hB⟩ :=
    exists_stageTests_crossRepresentation_path_approx sigma hsigma
      (protectedPrefix s.right step) (transportBudget_pos step)
  let requestLeft : Finset Limit :=
    stageTests nb ∪ (densePrefix step).image (innerAt s.right).symm
  have hmin : 0 < min db (transportBudget step) := lt_min hdb (transportBudget_pos step)
  obtain ⟨u, pu, husmall, huapprox⟩ := s.move requestLeft _ hmin
  let left' : unitary Limit := u * s.left
  let leftSegment : Path s.left left' :=
    { toFun := fun t => pu t * s.left
      continuous_toFun := by fun_prop
      source' := by rw [pu.source]; simp
      target' := by rw [pu.target] }
  let leftPath' : Path 1 left' := s.leftPath.trans leftSegment
  have hleft'Unit : ‖rho (left' : Limit) xi‖ = 1 := by
    rw [(rho (left' : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem rho left'.property), hxi]
  obtain ⟨na, da, hda, hA⟩ :=
    exists_stageTests_crossRepresentation_path_approx rho hrho
      (protectedPrefix left' (step + 1)) (transportBudget_pos (step + 1))
  have hBclose : ∀ i j : Fin (2 ^ nb),
      ‖Representation.vectorFunctional sigma (sigma (s.right : Limit) eta)
            (limitMatrixUnit nb i j) -
        Representation.vectorFunctional rho (rho (left' : Limit) xi)
            (limitMatrixUnit nb i j)‖ < db := by
    intro i j
    have h := huapprox (limitMatrixUnit nb i j)
      (Finset.mem_union_left _ (mem_stageTests nb i j))
    have hsimp : rho (u : Limit) (rho (s.left : Limit) xi) =
        rho (left' : Limit) xi := by
      change rho (u : Limit) (rho (s.left : Limit) xi) =
        rho ((u : Limit) * (s.left : Limit)) xi
      rw [map_mul, mul_apply_eq_comp]
    rw [hsimp, norm_sub_rev] at h
    exact lt_of_lt_of_le h (min_le_left _ _)
  obtain ⟨v, pv, hvsmall, hvapprox⟩ :=
    hB rho (sigma (s.right : Limit) eta) (rho (left' : Limit) xi)
      hrightUnit hleft'Unit hBclose (stageTests na) da hda
  let right' : unitary Limit := v * s.right
  let rightSegment : Path s.right right' :=
    { toFun := fun t => pv t * s.right
      continuous_toFun := by fun_prop
      source' := by rw [pv.source]; simp
      target' := by rw [pv.target] }
  let rightPath' : Path 1 right' := s.rightPath.trans rightSegment
  have hright'Unit : ‖sigma (right' : Limit) eta‖ = 1 := by
    rw [(sigma (right' : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem sigma right'.property), heta]
  have hAclose : ∀ i j : Fin (2 ^ na),
      ‖Representation.vectorFunctional rho (rho (left' : Limit) xi)
            (limitMatrixUnit na i j) -
        Representation.vectorFunctional sigma (sigma (right' : Limit) eta)
            (limitMatrixUnit na i j)‖ < da := by
    intro i j
    have h := hvapprox (limitMatrixUnit na i j) (mem_stageTests na i j)
    have hsimp : sigma (v : Limit) (sigma (s.right : Limit) eta) =
        sigma (right' : Limit) eta := by
      change sigma (v : Limit) (sigma (s.right : Limit) eta) =
        sigma ((v : Limit) * (s.right : Limit)) eta
      rw [map_mul, mul_apply_eq_comp]
    rw [hsimp, norm_sub_rev] at h
    exact h
  let next : AlternatingState rho sigma xi eta (step + 1) :=
    { left := left'
      right := right'
      leftPath := leftPath'
      rightPath := rightPath'
      move := hA sigma (rho (left' : Limit) xi) (sigma (right' : Limit) eta)
        hleft'Unit hright'Unit hAclose }
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
  have h := huapprox ((innerAt s.right).symm (transportDense j))
    (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨transportDense j, mem_densePrefix hj, rfl⟩))
  have hsimp : rho (u : Limit) (rho (s.left : Limit) xi) =
      rho (next.left : Limit) xi := by
    change rho (u : Limit) (rho (s.left : Limit) xi) =
      rho ((u : Limit) * (s.left : Limit)) xi
    rw [map_mul, mul_apply_eq_comp]
  rw [hsimp] at h
  exact lt_of_lt_of_le h (min_le_right _ _)

set_option maxHeartbeats 1600000 in
theorem nonempty_initialState
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    Nonempty (AlternatingState rho sigma xi eta 0) := by
  classical
  obtain ⟨nb, db, hdb, hB⟩ :=
    exists_stageTests_crossRepresentation_path_approx sigma hsigma
      (protectedPrefix 1 0) (transportBudget_pos 0)
  obtain ⟨u, pu, hu⟩ := exists_unitary_crossRepresentation_path_approx
    rho hrho sigma xi eta hxi heta (stageTests nb) hdb
  let left' : unitary Limit := u
  have hleft'Unit : ‖rho (left' : Limit) xi‖ = 1 := by
    rw [(rho (left' : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem rho left'.property), hxi]
  obtain ⟨na, da, hda, hA⟩ :=
    exists_stageTests_crossRepresentation_path_approx rho hrho
      (protectedPrefix left' 0) (transportBudget_pos 0)
  have hBclose : ∀ i j : Fin (2 ^ nb),
      ‖Representation.vectorFunctional sigma eta (limitMatrixUnit nb i j) -
        Representation.vectorFunctional rho (rho (left' : Limit) xi)
          (limitMatrixUnit nb i j)‖ < db := by
    intro i j
    have h := hu (limitMatrixUnit nb i j) (mem_stageTests nb i j)
    change ‖Representation.vectorFunctional sigma eta (limitMatrixUnit nb i j) -
      Representation.vectorFunctional rho (rho (u : Limit) xi)
        (limitMatrixUnit nb i j)‖ < db
    rw [norm_sub_rev]
    exact h
  obtain ⟨v, pv, _hvsmall, hvapprox⟩ :=
    hB rho eta (rho (left' : Limit) xi) heta hleft'Unit hBclose
      (stageTests na) da hda
  let right' : unitary Limit := v
  have hright'Unit : ‖sigma (right' : Limit) eta‖ = 1 := by
    rw [(sigma (right' : Limit)).norm_map_of_mem_unitary
      (Unitary.map_mem sigma right'.property), heta]
  have hAclose : ∀ i j : Fin (2 ^ na),
      ‖Representation.vectorFunctional rho (rho (left' : Limit) xi)
            (limitMatrixUnit na i j) -
        Representation.vectorFunctional sigma (sigma (right' : Limit) eta)
            (limitMatrixUnit na i j)‖ < da := by
    intro i j
    have h := hvapprox (limitMatrixUnit na i j) (mem_stageTests na i j)
    change ‖Representation.vectorFunctional rho (rho (left' : Limit) xi)
        (limitMatrixUnit na i j) -
      Representation.vectorFunctional sigma (sigma (v : Limit) eta)
        (limitMatrixUnit na i j)‖ < da
    rw [norm_sub_rev]
    exact h
  exact ⟨{
    left := left'
    right := right'
    leftPath := pu
    rightPath := pv
    move := hA sigma (rho (left' : Limit) xi) (sigma (right' : Limit) eta)
      hleft'Unit hright'Unit hAclose }⟩

noncomputable def initialState
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    AlternatingState rho sigma xi eta 0 :=
  Classical.choice (nonempty_initialState rho hrho sigma hsigma xi eta hxi heta)

noncomputable def chosenTransition
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    {step : ℕ} (s : AlternatingState rho sigma xi eta step) :
    AlternatingTransition rho sigma xi eta s :=
  Classical.choice (nonempty_transition rho hrho sigma hsigma xi eta hxi heta s)

noncomputable def alternatingStates
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1) :
    (n : ℕ) → AlternatingState rho sigma xi eta n
  | 0 => initialState rho hrho sigma hsigma xi eta hxi heta
  | n + 1 => (chosenTransition rho hrho sigma hsigma xi eta hxi heta
      (alternatingStates rho hrho sigma hsigma xi eta hxi heta n)).next

noncomputable def alternatingTransitions
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)
    (n : ℕ) :
    AlternatingTransition rho sigma xi eta
      (alternatingStates rho hrho sigma hsigma xi eta hxi heta n) :=
  chosenTransition rho hrho sigma hsigma xi eta hxi heta
    (alternatingStates rho hrho sigma hsigma xi eta hxi heta n)

section Sequences

variable {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (sigma : Representation Limit K) (hsigma : StarAlgHom.IsIrreducible sigma)
    (xi : H) (eta : K) (hxi : ‖xi‖ = 1) (heta : ‖eta‖ = 1)

local notation "S" => alternatingStates rho hrho sigma hsigma xi eta hxi heta
local notation "T" => alternatingTransitions rho hrho sigma hsigma xi eta hxi heta

/-- Integer-time vertices of the left concatenated path.  Negative times are
constant, time zero is the unit, and time `n+1` is the `n`th recursion state. -/
noncomputable def leftPathPoints : ℤ → unitary Limit
  | .ofNat 0 => 1
  | .ofNat (n + 1) => (S n).left
  | .negSucc _ => 1

/-- Integer-time vertices of the right concatenated path. -/
noncomputable def rightPathPoints : ℤ → unitary Limit
  | .ofNat 0 => 1
  | .ofNat (n + 1) => (S n).right
  | .negSucc _ => 1

/-- A correction path, translated on the right by the previous accumulated
unitary. -/
def translatedCorrectionPath {u w : unitary Limit} (p : Path 1 u) :
    Path w (u * w) :=
  { toFun := fun t => p t * w
    continuous_toFun := by fun_prop
    source' := by rw [p.source]; simp
    target' := by rw [p.target] }

/-- Unit-interval pieces of the left unbounded path. -/
noncomputable def leftPathSegments :
    (z : ℤ) → Path
      (leftPathPoints rho hrho sigma hsigma xi eta hxi heta z)
      (leftPathPoints rho hrho sigma hsigma xi eta hxi heta (z + 1))
  | .ofNat 0 => (S 0).leftPath
  | .ofNat (n + 1) => by
      let q : Path (S n).left ((T n).leftCorrection * (S n).left) :=
        translatedCorrectionPath (w := (S n).left) (T n).leftCorrectionPath
      exact q.cast (by simp [leftPathPoints]) (by
        simp only [leftPathPoints]
        change (S (n + 1)).left = (T n).leftCorrection * (S n).left
        exact (T n).next_left)
  | .negSucc n => by
      have hz : Int.negSucc n + 1 =
          match n with
          | 0 => (0 : ℤ)
          | k + 1 => Int.negSucc k := by
        cases n <;> simp [Int.negSucc_eq]
      rw [hz]
      cases n <;> exact Path.refl _

/-- Unit-interval pieces of the right unbounded path. -/
noncomputable def rightPathSegments :
    (z : ℤ) → Path
      (rightPathPoints rho hrho sigma hsigma xi eta hxi heta z)
      (rightPathPoints rho hrho sigma hsigma xi eta hxi heta (z + 1))
  | .ofNat 0 => (S 0).rightPath
  | .ofNat (n + 1) => by
      let q : Path (S n).right ((T n).rightCorrection * (S n).right) :=
        translatedCorrectionPath (w := (S n).right) (T n).rightCorrectionPath
      exact q.cast (by simp [rightPathPoints]) (by
        simp only [rightPathPoints]
        change (S (n + 1)).right = (T n).rightCorrection * (S n).right
        exact (T n).next_right)
  | .negSucc n => by
      have hz : Int.negSucc n + 1 =
          match n with
          | 0 => (0 : ℤ)
          | k + 1 => Int.negSucc k := by
        cases n <;> simp [Int.negSucc_eq]
      rw [hz]
      cases n <;> exact Path.refl _

/-- The left locally finite concatenation, constant at negative times. -/
noncomputable def leftContinuousPath (t : ℝ) : unitary Limit :=
  MathlibAnnex.Path.infiniteConcat
    (leftPathPoints rho hrho sigma hsigma xi eta hxi heta)
    (leftPathSegments rho hrho sigma hsigma xi eta hxi heta) t

/-- The right locally finite concatenation, constant at negative times. -/
noncomputable def rightContinuousPath (t : ℝ) : unitary Limit :=
  MathlibAnnex.Path.infiniteConcat
    (rightPathPoints rho hrho sigma hsigma xi eta hxi heta)
    (rightPathSegments rho hrho sigma hsigma xi eta hxi heta) t

theorem continuous_leftContinuousPath :
    Continuous (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta) :=
  MathlibAnnex.Path.continuous_infiniteConcat _ _

theorem continuous_rightContinuousPath :
    Continuous (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta) :=
  MathlibAnnex.Path.continuous_infiniteConcat _ _

theorem leftContinuousPath_zero :
    leftContinuousPath rho hrho sigma hsigma xi eta hxi heta 0 = 1 := by
  rw [leftContinuousPath, MathlibAnnex.Path.infiniteConcat, Int.floor_zero]
  change (S 0).leftPath
    ⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ = 1
  rw [show (⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ :
      unitInterval) = 0 by ext; norm_num [Int.fract]]
  exact (S 0).leftPath.source

theorem rightContinuousPath_zero :
    rightContinuousPath rho hrho sigma hsigma xi eta hxi heta 0 = 1 := by
  rw [rightContinuousPath, MathlibAnnex.Path.infiniteConcat, Int.floor_zero]
  change (S 0).rightPath
    ⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ = 1
  rw [show (⟨Int.fract (0 : ℝ), unitInterval.fract_mem (0 : ℝ)⟩ :
      unitInterval) = 0 by ext; norm_num [Int.fract]]
  exact (S 0).rightPath.source

theorem leftContinuousPath_segment (n : ℕ)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t =
      (T n).leftCorrectionPath
          ⟨(t : ℝ) - (n + 1), by
            constructor
            · exact sub_nonneg.mpr (by simpa using t.property.1)
            · apply (sub_le_iff_le_add).mpr
              have ht := t.property.2
              linarith⟩ *
        (S n).left := by
  let tz : Set.Icc ((Int.ofNat (n + 1) : ℤ) : ℝ)
      ((Int.ofNat (n + 1) : ℤ) + 1 : ℝ) :=
    ⟨t, by
      constructor
      · simpa using t.property.1
      · have ht := t.property.2
        norm_num at ht ⊢
        linarith⟩
  have h := MathlibAnnex.Path.infiniteConcat_eq_intervalPath
    (leftPathPoints rho hrho sigma hsigma xi eta hxi heta)
    (leftPathSegments rho hrho sigma hsigma xi eta hxi heta)
    (Int.ofNat (n + 1)) tz
  dsimp only [tz] at h
  convert h using 1 <;>
    simp [leftContinuousPath, MathlibAnnex.Path.intervalPath,
      leftPathSegments, translatedCorrectionPath, Path.cast]
  congr 2

theorem rightContinuousPath_segment (n : ℕ)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t =
      (T n).rightCorrectionPath
          ⟨(t : ℝ) - (n + 1), by
            constructor
            · exact sub_nonneg.mpr (by simpa using t.property.1)
            · apply (sub_le_iff_le_add).mpr
              have ht := t.property.2
              linarith⟩ *
        (S n).right := by
  let tz : Set.Icc ((Int.ofNat (n + 1) : ℤ) : ℝ)
      ((Int.ofNat (n + 1) : ℤ) + 1 : ℝ) :=
    ⟨t, by
      constructor
      · simpa using t.property.1
      · have ht := t.property.2
        norm_num at ht ⊢
        linarith⟩
  have h := MathlibAnnex.Path.infiniteConcat_eq_intervalPath
    (rightPathPoints rho hrho sigma hsigma xi eta hxi heta)
    (rightPathSegments rho hrho sigma hsigma xi eta hxi heta)
    (Int.ofNat (n + 1)) tz
  dsimp only [tz] at h
  convert h using 1 <;>
    simp [rightContinuousPath, MathlibAnnex.Path.intervalPath,
      rightPathSegments, translatedCorrectionPath, Path.cast]
  congr 2

noncomputable def leftAutomorphisms (n : ℕ) : StarAlgEquiv ℂ Limit Limit :=
  innerAt (S n).left

noncomputable def rightAutomorphisms (n : ℕ) : StarAlgEquiv ℂ Limit Limit :=
  innerAt (S n).right

theorem leftContinuousPath_forward_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)
          (transportDense j) -
        leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
          (transportDense j)‖ ≤ transportBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [leftContinuousPath_segment rho hrho sigma hsigma xi eta hxi heta n t]
  have hformula :
      innerAt ((T n).leftCorrectionPath s * (S n).left) (transportDense j) =
        innerAt (S n).left
          (star ((T n).leftCorrectionPath s : Limit) * transportDense j *
            ((T n).leftCorrectionPath s : Limit)) := by
    simp [innerAt, mul_assoc]
  rw [hformula, leftAutomorphisms]
  calc
    _ = ‖star ((T n).leftCorrectionPath s : Limit) * transportDense j *
          ((T n).leftCorrectionPath s : Limit) - transportDense j‖ := by
      have h := (StarAlgEquiv.isometry (innerAt (S n).left)).dist_eq
        (star ((T n).leftCorrectionPath s : Limit) * transportDense j *
          ((T n).leftCorrectionPath s : Limit)) (transportDense j)
      simpa only [dist_eq_norm] using h
    _ ≤ transportBudget n :=
      le_of_lt (((T n).left_small s _ (mem_protectedPrefix hj)).2)

theorem leftContinuousPath_inverse_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖(innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm
          (transportDense j) -
        (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm
          (transportDense j)‖ ≤ transportBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [leftContinuousPath_segment rho hrho sigma hsigma xi eta hxi heta n t]
  have hformula :
      (innerAt ((T n).leftCorrectionPath s * (S n).left)).symm
          (transportDense j) =
        ((T n).leftCorrectionPath s : Limit) *
          (innerAt (S n).left).symm (transportDense j) *
            star ((T n).leftCorrectionPath s : Limit) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change (((T n).leftCorrectionPath s : Limit) * (S n).left) *
        transportDense j *
          star (((T n).leftCorrectionPath s : Limit) * (S n).left) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula, leftAutomorphisms]
  exact le_of_lt (((T n).left_small s _ (mem_symm_protectedPrefix hj)).1)

theorem rightContinuousPath_forward_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)
          (transportDense j) -
        rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
          (transportDense j)‖ ≤ transportBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [rightContinuousPath_segment rho hrho sigma hsigma xi eta hxi heta n t]
  have hformula :
      innerAt ((T n).rightCorrectionPath s * (S n).right) (transportDense j) =
        innerAt (S n).right
          (star ((T n).rightCorrectionPath s : Limit) * transportDense j *
            ((T n).rightCorrectionPath s : Limit)) := by
    simp [innerAt, mul_assoc]
  rw [hformula, rightAutomorphisms]
  calc
    _ = ‖star ((T n).rightCorrectionPath s : Limit) * transportDense j *
          ((T n).rightCorrectionPath s : Limit) - transportDense j‖ := by
      have h := (StarAlgEquiv.isometry (innerAt (S n).right)).dist_eq
        (star ((T n).rightCorrectionPath s : Limit) * transportDense j *
          ((T n).rightCorrectionPath s : Limit)) (transportDense j)
      simpa only [dist_eq_norm] using h
    _ ≤ transportBudget n :=
      le_of_lt (((T n).right_small s _ (mem_protectedPrefix hj)).2)

theorem rightContinuousPath_inverse_dense_segment (n j : ℕ) (hj : j ≤ n)
    (t : Set.Icc ((n + 1 : ℕ) : ℝ) (n + 2 : ℝ)) :
    ‖(innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm
          (transportDense j) -
        (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm
          (transportDense j)‖ ≤ transportBudget n := by
  let s : unitInterval :=
    ⟨(t : ℝ) - (n + 1), by
      constructor
      · exact sub_nonneg.mpr (by simpa using t.property.1)
      · apply (sub_le_iff_le_add).mpr
        linarith [t.property.2]⟩
  rw [rightContinuousPath_segment rho hrho sigma hsigma xi eta hxi heta n t]
  have hformula :
      (innerAt ((T n).rightCorrectionPath s * (S n).right)).symm
          (transportDense j) =
        ((T n).rightCorrectionPath s : Limit) *
          (innerAt (S n).right).symm (transportDense j) *
            star ((T n).rightCorrectionPath s : Limit) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change (((T n).rightCorrectionPath s : Limit) * (S n).right) *
        transportDense j *
          star (((T n).rightCorrectionPath s : Limit) * (S n).right) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula, rightAutomorphisms]
  exact le_of_lt (((T n).right_small s _ (mem_symm_protectedPrefix hj)).1)

theorem leftAutomorphisms_step (n j : ℕ) (hj : j ≤ n) :
    ‖leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)
          (transportDense j) -
      leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
          (transportDense j)‖ ≤ transportBudget n := by
  let t := T n
  have hnext : S (n + 1) = t.next := rfl
  rw [leftAutomorphisms, leftAutomorphisms, hnext, t.next_left]
  have hformula :
      innerAt (t.leftCorrection * (S n).left) (transportDense j) =
        innerAt (S n).left
          (star (t.leftCorrection : Limit) * transportDense j *
            (t.leftCorrection : Limit)) := by
    simp [innerAt, mul_assoc]
  rw [hformula]
  calc
    _ = ‖star (t.leftCorrection : Limit) * transportDense j *
          (t.leftCorrection : Limit) - transportDense j‖ := by
      have h := (StarAlgEquiv.isometry (innerAt (S n).left)).dist_eq
        (star (t.leftCorrection : Limit) * transportDense j *
          (t.leftCorrection : Limit)) (transportDense j)
      simpa only [dist_eq_norm] using h
    _ ≤ transportBudget n := by
      have h := (t.left_small (1 : Set.Icc (0 : ℝ) 1) _
        (mem_protectedPrefix hj)).2
      simpa only [t.leftCorrectionPath.target] using le_of_lt h

theorem leftAutomorphisms_symm_step (n j : ℕ) (hj : j ≤ n) :
    ‖(leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)).symm
          (transportDense j) -
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm
          (transportDense j)‖ ≤ transportBudget n := by
  let t := T n
  have hnext : S (n + 1) = t.next := rfl
  rw [leftAutomorphisms, leftAutomorphisms, hnext, t.next_left]
  have hformula :
      (innerAt (t.leftCorrection * (S n).left)).symm (transportDense j) =
        (t.leftCorrection : Limit) *
          (innerAt (S n).left).symm (transportDense j) *
            star (t.leftCorrection : Limit) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change ((t.leftCorrection : Limit) * (S n).left) * transportDense j *
        star ((t.leftCorrection : Limit) * (S n).left) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula]
  have h := (t.left_small (1 : Set.Icc (0 : ℝ) 1) _
    (mem_symm_protectedPrefix hj)).1
  simpa only [t.leftCorrectionPath.target] using le_of_lt h

theorem rightAutomorphisms_step (n j : ℕ) (hj : j ≤ n) :
    ‖rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)
          (transportDense j) -
      rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
          (transportDense j)‖ ≤ transportBudget n := by
  let t := T n
  have hnext : S (n + 1) = t.next := rfl
  rw [rightAutomorphisms, rightAutomorphisms, hnext, t.next_right]
  have hformula :
      innerAt (t.rightCorrection * (S n).right) (transportDense j) =
        innerAt (S n).right
          (star (t.rightCorrection : Limit) * transportDense j *
            (t.rightCorrection : Limit)) := by
    simp [innerAt, mul_assoc]
  rw [hformula]
  calc
    _ = ‖star (t.rightCorrection : Limit) * transportDense j *
          (t.rightCorrection : Limit) - transportDense j‖ := by
      have h := (StarAlgEquiv.isometry (innerAt (S n).right)).dist_eq
        (star (t.rightCorrection : Limit) * transportDense j *
          (t.rightCorrection : Limit)) (transportDense j)
      simpa only [dist_eq_norm] using h
    _ ≤ transportBudget n := by
      have h := (t.right_small (1 : Set.Icc (0 : ℝ) 1) _
        (mem_protectedPrefix hj)).2
      simpa only [t.rightCorrectionPath.target] using le_of_lt h

theorem rightAutomorphisms_symm_step (n j : ℕ) (hj : j ≤ n) :
    ‖(rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)).symm
          (transportDense j) -
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm
          (transportDense j)‖ ≤ transportBudget n := by
  let t := T n
  have hnext : S (n + 1) = t.next := rfl
  rw [rightAutomorphisms, rightAutomorphisms, hnext, t.next_right]
  have hformula :
      (innerAt (t.rightCorrection * (S n).right)).symm (transportDense j) =
        (t.rightCorrection : Limit) *
          (innerAt (S n).right).symm (transportDense j) *
            star (t.rightCorrection : Limit) := by
    rw [innerAt, Unitary.conjStarAlgAut_symm,
      innerAt, Unitary.conjStarAlgAut_symm]
    simp only [Unitary.conjStarAlgAut_apply, star_star]
    change ((t.rightCorrection : Limit) * (S n).right) * transportDense j *
        star ((t.rightCorrection : Limit) * (S n).right) = _
    simp only [star_mul]
    noncomm_ring
  rw [hformula]
  have h := (t.right_small (1 : Set.Icc (0 : ℝ) 1) _
    (mem_symm_protectedPrefix hj)).1
  simpa only [t.rightCorrectionPath.target] using le_of_lt h

theorem leftAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n =>
      leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a) :=
  MathlibAnnex.CStarAlgebra.cauchySeq_of_summable_dense_steps
    transportDense denseRange_transportDense
    (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    transportBudget summable_transportBudget
    (leftAutomorphisms_step rho hrho sigma hsigma xi eta hxi heta)

theorem leftAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a) :=
  MathlibAnnex.CStarAlgebra.cauchySeq_of_summable_dense_steps
    transportDense denseRange_transportDense
    (fun n => (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    transportBudget summable_transportBudget
    (leftAutomorphisms_symm_step rho hrho sigma hsigma xi eta hxi heta)

theorem rightAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n =>
      rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a) :=
  MathlibAnnex.CStarAlgebra.cauchySeq_of_summable_dense_steps
    transportDense denseRange_transportDense
    (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    transportBudget summable_transportBudget
    (rightAutomorphisms_step rho hrho sigma hsigma xi eta hxi heta)

theorem rightAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a) :=
  MathlibAnnex.CStarAlgebra.cauchySeq_of_summable_dense_steps
    transportDense denseRange_transportDense
    (fun n => (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    transportBudget summable_transportBudget
    (rightAutomorphisms_symm_step rho hrho sigma hsigma xi eta hxi heta)

theorem tendsto_transportBudget_zero :
    Tendsto transportBudget atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The two-sided pointwise limit of the accumulated left conjugations. -/
noncomputable def leftLimitAutomorphism : StarAlgEquiv ℂ Limit Limit :=
  MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit
    (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    (leftAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta)
    (leftAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta)

/-- The two-sided pointwise limit of the accumulated right conjugations. -/
noncomputable def rightLimitAutomorphism : StarAlgEquiv ℂ Limit Limit :=
  MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit
    (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    (rightAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta)
    (rightAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta)

theorem tendsto_leftContinuousPath_forward (a : Limit) :
    Tendsto (fun t : ℝ =>
        innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t) a)
      atTop (nhds (leftLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    transportDense denseRange_transportDense
    (fun n a => leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a)
    (fun t => innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t))
    (fun n => StarAlgEquiv.isometry
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n))
    (fun t => StarAlgEquiv.isometry
      (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)))
    transportBudget tendsto_transportBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        leftContinuousPath_forward_dense_segment
          rho hrho sigma hsigma xi eta hxi heta n j hj t)
    a _
  simpa [leftLimitAutomorphism,
    MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_apply,
    MathlibAnnex.CStarAlgebra.pointwiseLimitHom_apply] using
    MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
      (leftAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta) a

theorem tendsto_leftContinuousPath_inverse (a : Limit) :
    Tendsto (fun t : ℝ =>
        (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm a)
      atTop (nhds ((leftLimitAutomorphism
        rho hrho sigma hsigma xi eta hxi heta).symm a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    transportDense denseRange_transportDense
    (fun n a =>
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a)
    (fun t => (innerAt
      (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm)
    (fun n => StarAlgEquiv.isometry
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    (fun t => StarAlgEquiv.isometry
      (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm)
    transportBudget tendsto_transportBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        leftContinuousPath_inverse_dense_segment
          rho hrho sigma hsigma xi eta hxi heta n j hj t)
    a _
  rw [leftLimitAutomorphism,
    MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_symm_apply]
  exact MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
    (fun n => (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    (leftAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta) a

theorem tendsto_rightContinuousPath_forward (a : Limit) :
    Tendsto (fun t : ℝ =>
        innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t) a)
      atTop (nhds (rightLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    transportDense denseRange_transportDense
    (fun n a => rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a)
    (fun t => innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t))
    (fun n => StarAlgEquiv.isometry
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n))
    (fun t => StarAlgEquiv.isometry
      (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)))
    transportBudget tendsto_transportBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        rightContinuousPath_forward_dense_segment
          rho hrho sigma hsigma xi eta hxi heta n j hj t)
    a _
  simpa [rightLimitAutomorphism,
    MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_apply,
    MathlibAnnex.CStarAlgebra.pointwiseLimitHom_apply] using
    MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
      (rightAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta) a

theorem tendsto_rightContinuousPath_inverse (a : Limit) :
    Tendsto (fun t : ℝ =>
        (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm a)
      atTop (nhds ((rightLimitAutomorphism
        rho hrho sigma hsigma xi eta hxi heta).symm a)) := by
  apply MathlibAnnex.Metric.tendsto_atTop_of_isometry_segment_approx
    transportDense denseRange_transportDense
    (fun n a =>
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a)
    (fun t => (innerAt
      (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm)
    (fun n => StarAlgEquiv.isometry
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    (fun t => StarAlgEquiv.isometry
      (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm)
    transportBudget tendsto_transportBudget_zero
    (fun n j hj t => by
      simpa only [dist_eq_norm] using
        rightContinuousPath_inverse_dense_segment
          rho hrho sigma hsigma xi eta hxi heta n j hj t)
    a _
  rw [rightLimitAutomorphism,
    MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_symm_apply]
  exact MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
    (fun n => (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    (rightAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta) a

noncomputable def outputUnitary (n : ℕ) : unitary Limit :=
  star (S (n + 1)).left * (S n).right

noncomputable def outputAutomorphisms (n : ℕ) : StarAlgEquiv ℂ Limit Limit :=
  Unitary.conjStarAlgAut ℂ Limit
    (outputUnitary rho hrho sigma hsigma xi eta hxi heta n)

theorem outputAutomorphisms_eq (n : ℕ) :
    outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n =
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm.trans
        (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)) := by
  ext a
  simp [outputAutomorphisms, outputUnitary, rightAutomorphisms,
    leftAutomorphisms, innerAt, mul_assoc]

theorem leftAutomorphisms_succ_cauchy :
    ∀ a, CauchySeq (fun n =>
      leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1) a) := by
  intro a
  exact (cauchySeq_shift 1).2
    (leftAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta a)

theorem leftAutomorphisms_succ_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)).symm a) := by
  intro a
  exact (cauchySeq_shift 1).2
    (leftAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta a)

theorem outputAutomorphisms_cauchy :
    ∀ a, CauchySeq (fun n =>
      outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a) := by
  intro a
  have h := MathlibAnnex.CStarAlgebra.cauchySeq_trans_of_isometry
    (fun n => leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1))
    (fun n => (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm)
    (leftAutomorphisms_succ_cauchy rho hrho sigma hsigma xi eta hxi heta)
    (rightAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta) a
  simpa only [outputAutomorphisms_eq] using h

theorem outputAutomorphisms_symm_cauchy :
    ∀ a, CauchySeq (fun n =>
      (outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a) := by
  intro a
  have h := MathlibAnnex.CStarAlgebra.cauchySeq_trans_of_isometry
    (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    (fun n =>
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)).symm)
    (rightAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta)
    (leftAutomorphisms_succ_symm_cauchy rho hrho sigma hsigma xi eta hxi heta) a
  have heq : ∀ n,
      (outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm =
        (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)).symm.trans
          (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n) := by
    intro n
    rw [outputAutomorphisms_eq]
    rfl
  simpa only [heq] using h

theorem outputAutomorphisms_state_dense (n j : ℕ) (hj : j ≤ n) :
    ‖Representation.vectorFunctional rho xi
          (outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
            (transportDense j)) -
      Representation.vectorFunctional sigma eta (transportDense j)‖ <
        transportBudget n := by
  let t := T n
  have hnext : S (n + 1) = t.next := rfl
  have h := t.state_small j hj
  rw [← hnext] at h
  rw [Representation.vectorFunctional_map_apply,
    Representation.vectorFunctional_map_apply] at h
  have h' :
      ‖Representation.vectorFunctional rho xi
            (innerAt (S (n + 1)).left
              ((innerAt (S n).right).symm (transportDense j))) -
        Representation.vectorFunctional sigma eta
            (innerAt (S n).right
              ((innerAt (S n).right).symm (transportDense j)))‖ <
          transportBudget n := by
    simpa [innerAt] using h
  have hleft :
      innerAt (S (n + 1)).left
          ((innerAt (S n).right).symm (transportDense j)) =
        outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n
          (transportDense j) := by
    rw [outputAutomorphisms_eq]
    rfl
  rw [hleft, (innerAt (S n).right).apply_symm_apply] at h'
  exact h'

theorem tendsto_outputAutomorphisms_state :
    ∀ a, Tendsto (fun n => Representation.vectorFunctional rho xi
        (outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta n a))
      atTop (nhds (Representation.vectorFunctional sigma eta a)) := by
  apply MathlibAnnex.CStarAlgebra.tendsto_functional_of_dense_prefix
    transportDense denseRange_transportDense
    (outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
    (Representation.vectorFunctional rho xi)
    (Representation.vectorFunctional sigma eta)
    (Representation.norm_vectorFunctional_apply_le rho hxi)
    (Representation.norm_vectorFunctional_apply_le sigma heta)
    transportBudget tendsto_transportBudget_zero
  exact outputAutomorphisms_state_dense rho hrho sigma hsigma xi eta hxi heta

/-- The common limit written using equal-time left and right limits. -/
noncomputable def asymptoticAutomorphism : StarAlgEquiv ℂ Limit Limit :=
  (rightLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta).symm.trans
    (leftLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta)

/-- The norm-continuous implementing unitary path. -/
noncomputable def implementingUnitary (t : ℝ) : unitary Limit :=
  star (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t) *
    rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t

noncomputable def implementingAutomorphism (t : ℝ) : StarAlgEquiv ℂ Limit Limit :=
  Unitary.conjStarAlgAut ℂ Limit
    (implementingUnitary rho hrho sigma hsigma xi eta hxi heta t)

theorem continuous_implementingUnitary :
    Continuous (implementingUnitary rho hrho sigma hsigma xi eta hxi heta) := by
  unfold implementingUnitary
  change Continuous (fun t =>
    (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)⁻¹ *
      rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)
  exact (continuous_leftContinuousPath
    rho hrho sigma hsigma xi eta hxi heta).inv.mul
      (continuous_rightContinuousPath rho hrho sigma hsigma xi eta hxi heta)

theorem implementingUnitary_zero :
    implementingUnitary rho hrho sigma hsigma xi eta hxi heta 0 = 1 := by
  simp [implementingUnitary,
    leftContinuousPath_zero rho hrho sigma hsigma xi eta hxi heta,
    rightContinuousPath_zero rho hrho sigma hsigma xi eta hxi heta]

theorem implementingAutomorphism_eq (t : ℝ) :
    implementingAutomorphism rho hrho sigma hsigma xi eta hxi heta t =
      (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm.trans
        (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)) := by
  ext a
  simp [implementingAutomorphism, implementingUnitary, innerAt, mul_assoc]

theorem implementingAutomorphism_symm_eq (t : ℝ) :
    (implementingAutomorphism rho hrho sigma hsigma xi eta hxi heta t).symm =
      (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm.trans
        (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)) := by
  rw [implementingAutomorphism_eq]
  rfl

theorem tendsto_outputAutomorphisms_asymptoticAutomorphism (a : Limit) :
    Tendsto (fun n => outputAutomorphisms
        rho hrho sigma hsigma xi eta hxi heta n a)
      atTop (nhds (asymptoticAutomorphism
        rho hrho sigma hsigma xi eta hxi heta a)) := by
  have hright : Tendsto (fun n =>
      (rightAutomorphisms rho hrho sigma hsigma xi eta hxi heta n).symm a)
      atTop (nhds ((rightLimitAutomorphism
        rho hrho sigma hsigma xi eta hxi heta).symm a)) := by
    rw [rightLimitAutomorphism,
      MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_symm_apply]
    exact MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
      (fun n => (rightAutomorphisms
        rho hrho sigma hsigma xi eta hxi heta n).symm)
      (rightAutomorphisms_symm_cauchy
        rho hrho sigma hsigma xi eta hxi heta) a
  have hleft (b : Limit) : Tendsto (fun n =>
      leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1) b)
      atTop (nhds (leftLimitAutomorphism
        rho hrho sigma hsigma xi eta hxi heta b)) := by
    apply (tendsto_add_atTop_iff_nat
      (f := fun n => leftAutomorphisms
        rho hrho sigma hsigma xi eta hxi heta n b) 1).2
    simpa [leftLimitAutomorphism,
      MathlibAnnex.CStarAlgebra.twoSidedPointwiseLimit_apply,
      MathlibAnnex.CStarAlgebra.pointwiseLimitHom_apply] using
      MathlibAnnex.CStarAlgebra.tendsto_pointwiseLimit
        (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta)
        (leftAutomorphisms_cauchy
          rho hrho sigma hsigma xi eta hxi heta) b
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun n => leftAutomorphisms
      rho hrho sigma hsigma xi eta hxi heta (n + 1))
    (fun n => (rightAutomorphisms
      rho hrho sigma hsigma xi eta hxi heta n).symm a)
    (fun n => StarAlgEquiv.isometry
      (leftAutomorphisms rho hrho sigma hsigma xi eta hxi heta (n + 1)))
    hright (hleft ((rightLimitAutomorphism
      rho hrho sigma hsigma xi eta hxi heta).symm a))
  simpa [outputAutomorphisms_eq, asymptoticAutomorphism] using hcomp

theorem tendsto_implementingAutomorphism (a : Limit) :
    Tendsto (fun t : ℝ =>
        implementingAutomorphism rho hrho sigma hsigma xi eta hxi heta t a)
      atTop (nhds (asymptoticAutomorphism
        rho hrho sigma hsigma xi eta hxi heta a)) := by
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun t => innerAt
      (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t))
    (fun t => (innerAt
      (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm a)
    (fun t => StarAlgEquiv.isometry
      (innerAt (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)))
    (tendsto_rightContinuousPath_inverse
      rho hrho sigma hsigma xi eta hxi heta a)
    (tendsto_leftContinuousPath_forward rho hrho sigma hsigma xi eta hxi heta
      ((rightLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta).symm a))
  simpa [implementingAutomorphism_eq, asymptoticAutomorphism] using hcomp

theorem tendsto_implementingAutomorphism_symm (a : Limit) :
    Tendsto (fun t : ℝ =>
        (implementingAutomorphism rho hrho sigma hsigma xi eta hxi heta t).symm a)
      atTop (nhds ((asymptoticAutomorphism
        rho hrho sigma hsigma xi eta hxi heta).symm a)) := by
  have hcomp := MathlibAnnex.Metric.tendsto_comp_of_isometry
    (fun t => innerAt
      (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t))
    (fun t => (innerAt
      (leftContinuousPath rho hrho sigma hsigma xi eta hxi heta t)).symm a)
    (fun t => StarAlgEquiv.isometry
      (innerAt (rightContinuousPath rho hrho sigma hsigma xi eta hxi heta t)))
    (tendsto_leftContinuousPath_inverse
      rho hrho sigma hsigma xi eta hxi heta a)
    (tendsto_rightContinuousPath_forward rho hrho sigma hsigma xi eta hxi heta
      ((leftLimitAutomorphism rho hrho sigma hsigma xi eta hxi heta).symm a))
  simpa [implementingAutomorphism_symm_eq, asymptoticAutomorphism] using hcomp

theorem asymptoticAutomorphism_state (a : Limit) :
    Representation.vectorFunctional rho xi
        (asymptoticAutomorphism rho hrho sigma hsigma xi eta hxi heta a) =
      Representation.vectorFunctional sigma eta a := by
  apply tendsto_nhds_unique
    ((Representation.vectorFunctional rho xi).continuous.tendsto _ |>.comp
      (tendsto_outputAutomorphisms_asymptoticAutomorphism
        rho hrho sigma hsigma xi eta hxi heta a))
  exact tendsto_outputAutomorphisms_state
    rho hrho sigma hsigma xi eta hxi heta a

include hrho hsigma hxi heta in
theorem asymptoticallyInner_vectorFunctional :
    ∃ alpha : StarAlgEquiv ℂ Limit Limit, ∃ U : ℝ → unitary Limit,
      Continuous U ∧ U 0 = 1 ∧
      (∀ a, Representation.vectorFunctional rho xi (alpha a) =
        Representation.vectorFunctional sigma eta a) ∧
      (∀ a, Tendsto (fun t => Unitary.conjStarAlgAut ℂ Limit (U t) a)
        atTop (nhds (alpha a))) ∧
      ∀ a, Tendsto (fun t =>
        (Unitary.conjStarAlgAut ℂ Limit (U t)).symm a)
        atTop (nhds (alpha.symm a)) := by
  exact ⟨asymptoticAutomorphism rho hrho sigma hsigma xi eta hxi heta,
    implementingUnitary rho hrho sigma hsigma xi eta hxi heta,
    continuous_implementingUnitary rho hrho sigma hsigma xi eta hxi heta,
    implementingUnitary_zero rho hrho sigma hsigma xi eta hxi heta,
    asymptoticAutomorphism_state rho hrho sigma hsigma xi eta hxi heta,
    tendsto_implementingAutomorphism rho hrho sigma hsigma xi eta hxi heta,
    tendsto_implementingAutomorphism_symm rho hrho sigma hsigma xi eta hxi heta⟩

include hrho hsigma hxi heta in
theorem hasInnerIntertwiningSequence_vectorFunctional :
    HasInnerIntertwiningSequence
      (Representation.vectorFunctional rho xi)
      (Representation.vectorFunctional sigma eta) := by
  refine ⟨outputAutomorphisms rho hrho sigma hsigma xi eta hxi heta,
    outputAutomorphisms_cauchy rho hrho sigma hsigma xi eta hxi heta,
    outputAutomorphisms_symm_cauchy rho hrho sigma hsigma xi eta hxi heta,
    ?_, tendsto_outputAutomorphisms_state rho hrho sigma hsigma xi eta hxi heta⟩
  intro n
  exact ⟨outputUnitary rho hrho sigma hsigma xi eta hxi heta n, rfl⟩

end Sequences

set_option maxHeartbeats 1600000 in
/-- Every pair of pure CAR states has a genuine two-sided inner
intertwining sequence. -/
theorem hasInnerIntertwiningSequence_of_pure
    (phi psi : Limit →L[ℂ] ℂ)
    (hphi : MathlibAnnex.CStarAlgebra.IsPureState Limit phi) (hpsi : MathlibAnnex.CStarAlgebra.IsPureState Limit psi) :
    HasInnerIntertwiningSequence phi psi := by
  have hphiState : phi ∈ stateSpace Limit := extremePoints_subset hphi
  let fphi := positiveLinearMapOfMemStateSpace phi hphiState
  let rho : Representation Limit fphi.GNS := fphi.gnsStarAlgHom
  let xi : fphi.GNS := fphi.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := by
    change ‖stateGNSVector phi hphiState‖ = 1
    exact norm_stateGNSVector phi hphiState
  letI : Nontrivial fphi.GNS := by
    apply nontrivial_of_ne xi 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [hxi, norm_zero] at hnorm
    norm_num at hnorm
  have hrho : StarAlgHom.IsIrreducible rho := by
    simpa [rho, fphi] using
      isIrreducible_pureState_gnsStarAlgHom phi hphiState hphi
  have hphiVF : Representation.vectorFunctional rho xi = phi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector phi hphiState)
      ((positiveLinearMapOfMemStateSpace phi hphiState).gnsStarAlgHom a
        (stateGNSVector phi hphiState)) = phi a
    exact inner_gnsStarAlgHom_stateGNSVector phi hphiState a
  have hpsiState : psi ∈ stateSpace Limit := extremePoints_subset hpsi
  let fpsi := positiveLinearMapOfMemStateSpace psi hpsiState
  let sigma : Representation Limit fpsi.GNS := fpsi.gnsStarAlgHom
  let eta : fpsi.GNS := fpsi.gnsCyclicVector
  have heta : ‖eta‖ = 1 := by
    change ‖stateGNSVector psi hpsiState‖ = 1
    exact norm_stateGNSVector psi hpsiState
  letI : Nontrivial fpsi.GNS := by
    apply nontrivial_of_ne eta 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [heta, norm_zero] at hnorm
    norm_num at hnorm
  have hsigma : StarAlgHom.IsIrreducible sigma := by
    simpa [sigma, fpsi] using
      isIrreducible_pureState_gnsStarAlgHom psi hpsiState hpsi
  have hpsiVF : Representation.vectorFunctional sigma eta = psi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector psi hpsiState)
      ((positiveLinearMapOfMemStateSpace psi hpsiState).gnsStarAlgHom a
        (stateGNSVector psi hpsiState)) = psi a
    exact inner_gnsStarAlgHom_stateGNSVector psi hpsiState a
  rw [← hphiVF, ← hpsiVF]
  exact hasInnerIntertwiningSequence_vectorFunctional
    rho hrho sigma hsigma xi eta hxi heta

set_option maxHeartbeats 1600000 in
/-- Every pair of pure CAR states is connected by one norm-continuous
unitary path whose inner automorphisms, and their actual inverses, converge
point-norm to the transporting automorphism and its inverse. -/
theorem asymptoticallyInnerPureStateHomogeneity : AsymptoticallyInnerPureStateHomogeneity := by
  intro phi psi hphi hpsi
  have hphiState : phi ∈ stateSpace Limit := extremePoints_subset hphi
  let fphi := positiveLinearMapOfMemStateSpace phi hphiState
  let rho : Representation Limit fphi.GNS := fphi.gnsStarAlgHom
  let xi : fphi.GNS := fphi.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := by
    change ‖stateGNSVector phi hphiState‖ = 1
    exact norm_stateGNSVector phi hphiState
  letI : Nontrivial fphi.GNS := by
    apply nontrivial_of_ne xi 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [hxi, norm_zero] at hnorm
    norm_num at hnorm
  have hrho : StarAlgHom.IsIrreducible rho := by
    simpa [rho, fphi] using
      isIrreducible_pureState_gnsStarAlgHom phi hphiState hphi
  have hphiVF : Representation.vectorFunctional rho xi = phi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector phi hphiState)
      ((positiveLinearMapOfMemStateSpace phi hphiState).gnsStarAlgHom a
        (stateGNSVector phi hphiState)) = phi a
    exact inner_gnsStarAlgHom_stateGNSVector phi hphiState a
  have hpsiState : psi ∈ stateSpace Limit := extremePoints_subset hpsi
  let fpsi := positiveLinearMapOfMemStateSpace psi hpsiState
  let sigma : Representation Limit fpsi.GNS := fpsi.gnsStarAlgHom
  let eta : fpsi.GNS := fpsi.gnsCyclicVector
  have heta : ‖eta‖ = 1 := by
    change ‖stateGNSVector psi hpsiState‖ = 1
    exact norm_stateGNSVector psi hpsiState
  letI : Nontrivial fpsi.GNS := by
    apply nontrivial_of_ne eta 0
    intro hzero
    have hnorm := congrArg norm hzero
    rw [heta, norm_zero] at hnorm
    norm_num at hnorm
  have hsigma : StarAlgHom.IsIrreducible sigma := by
    simpa [sigma, fpsi] using
      isIrreducible_pureState_gnsStarAlgHom psi hpsiState hpsi
  have hpsiVF : Representation.vectorFunctional sigma eta = psi := by
    apply ContinuousLinearMap.ext
    intro a
    rw [Representation.vectorFunctional_apply]
    change inner ℂ (stateGNSVector psi hpsiState)
      ((positiveLinearMapOfMemStateSpace psi hpsiState).gnsStarAlgHom a
        (stateGNSVector psi hpsiState)) = psi a
    exact inner_gnsStarAlgHom_stateGNSVector psi hpsiState a
  obtain ⟨alpha, U, hU, hU0, hstate, hforward, hinverse⟩ :=
    asymptoticallyInner_vectorFunctional
      rho hrho sigma hsigma xi eta hxi heta
  refine ⟨alpha, U, hU, hU0, ?_, hforward, hinverse⟩
  intro a
  rw [← hphiVF, ← hpsiVF]
  exact hstate a

/-- Regression adapter: forgetting the implementing path recovers the
previous CAR approximate-inner homogeneity statement. -/
theorem homogeneity_from_asymptotic : PureStateHomogeneity :=
  homogeneity_of_asymptoticallyInner asymptoticallyInnerPureStateHomogeneity

/-- The CAR homogeneity endpoint, with the intertwining supplier discharged. -/
theorem homogeneity : PureStateHomogeneity :=
  homogeneity_of_innerIntertwiningSequences
    (fun phi psi hphi hpsi =>
      hasInnerIntertwiningSequence_of_pure phi psi hphi hpsi)

end MathlibAnnex.CStarAlgebra.CAR
