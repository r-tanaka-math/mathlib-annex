import BanachGeometry.OperatorGraphs.GraphLinear
import BanachGeometry.SequenceSpaces.PairLp
import BanachGeometry.SequenceSpaces.C0Adapters

/-! R6 Proposition 6.3 on exactly the closed graph carrier of 6.1.
The domain coordinate uses ℓ₁(A_j × W); the image coordinate uses ℓ₂(B_j × W).
The output is the identity-on-pairs linear splitting with bounds 1 and 2,
and a contractively complemented isometric c₀(W).
Execution evidence is recorded in the external receipts. -/

noncomputable section
open Filter
namespace BanachGeometry
namespace GraphSplitting
variable (A B : ℕ → Type) (W : Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ)

abbrev Domain (j : ℕ) := WithLp 1 (A j × W)
abbrev Codomain (j : ℕ) := WithLp 2 (B j × W)

def tilde (j : ℕ) : Domain A W j →L[ℝ] Codomain B W j :=
  ((PairLp.left 2 (B j) W).comp (Q j)).comp (PairLp.first 1 (A j) W) +
    (PairLp.right 2 (B j) W).comp (PairLp.second 1 (A j) W)

theorem first_tilde (j : ℕ) (z : Domain A W j) :
    PairLp.first 2 (B j) W (tilde A B W Q j z) = Q j (PairLp.first 1 (A j) W z) := by
  simp only [tilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    map_add, PairLp.first_left, PairLp.first_right, add_zero]

theorem second_tilde (j : ℕ) (z : Domain A W j) :
    PairLp.second 2 (B j) W (tilde A B W Q j z) = PairLp.second 1 (A j) W z := by
  simp only [tilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    map_add, PairLp.second_left, PairLp.second_right, zero_add]

@[simp] theorem tilde_left (j : ℕ) (x : A j) :
    tilde A B W Q j (PairLp.left 1 (A j) W x) = PairLp.left 2 (B j) W (Q j x) := by
  simp only [tilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    PairLp.first_left, PairLp.second_left, map_zero, add_zero]

@[simp] theorem tilde_right (j : ℕ) (v : W) :
    tilde A B W Q j (PairLp.right 1 (A j) W v) = PairLp.right 2 (B j) W v := by
  simp only [tilde, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    PairLp.first_right, PairLp.second_right, map_zero, zero_add]

abbrev Y := WeightedGraph.Space A B Q «λ»
abbrev X := WeightedGraph.Space (Domain A W) (Codomain B W) (tilde A B W Q) «λ»

def forget : X A B W Q «λ» →L[ℝ] Y A B Q «λ» :=
  WeightedGraph.mapCLM (Domain A W) (Codomain B W) A B (tilde A B W Q) Q «λ»
    (fun j => PairLp.first 1 (A j) W) (fun j => PairLp.first 2 (B j) W)
    (fun j => PairLp.opNorm_first_le 1 (A j) W) (fun j => PairLp.opNorm_first_le 2 (B j) W)
    (by intro j; ext z; exact (first_tilde A B W Q j z).symm)

def second : X A B W Q «λ» →L[ℝ] C0Sum (fun _ : ℕ => W) :=
  (C0Linear.continuousLinearMap (fun j => PairLp.second 2 (B j) W) 1 zero_le_one
    (fun j => PairLp.opNorm_second_le 2 (B j) W)).comp
    (WeightedGraph.output (Domain A W) (Codomain B W) (tilde A B W Q) «λ»)

theorem norm_forget_le (x : X A B W Q «λ») : ‖forget A B W Q «λ» x‖ ≤ ‖x‖ :=
  WeightedGraph.norm_map_le (Domain A W) (Codomain B W) A B (tilde A B W Q) Q «λ»
    (fun j => PairLp.first 1 (A j) W) (fun j => PairLp.first 2 (B j) W)
    (fun j => PairLp.opNorm_first_le 1 (A j) W) (fun j => PairLp.opNorm_first_le 2 (B j) W)
    (by intro j; apply ContinuousLinearMap.ext; intro z; exact (first_tilde A B W Q j z).symm) x

theorem norm_second_le (x : X A B W Q «λ») : ‖second A B W Q «λ» x‖ ≤ ‖x‖ := by
  have h := C0Linear.norm_map_le (fun j => PairLp.second 2 (B j) W) 1 zero_le_one
    (fun j => PairLp.opNorm_second_le 2 (B j) W)
    (WeightedGraph.output (Domain A W) (Codomain B W) (tilde A B W Q) «λ» x)
  have h' : ‖second A B W Q «λ» x‖ ≤
      ‖WeightedGraph.output (Domain A W) (Codomain B W) (tilde A B W Q) «λ» x‖ := by
    change ‖C0Linear.map (fun j => PairLp.second 2 (B j) W) 1 zero_le_one
      (fun j => PairLp.opNorm_second_le 2 (B j) W)
      (WeightedGraph.output (Domain A W) (Codomain B W) (tilde A B W Q) «λ» x)‖ ≤ _
    simpa only [one_mul] using h
  exact h'.trans (WeightedGraph.norm_output_le _ _ _ _ x)

variable («hλ» : ∀ j, 0 < «λ» j)
include «hλ»

theorem coord_forget (j : ℕ) (x : X A B W Q «λ») :
    WeightedGraph.coord A B Q «λ» j (forget A B W Q «λ» x) =
      PairLp.first 1 (A j) W (WeightedGraph.coord _ _ (tilde A B W Q) «λ» j x) :=
  WeightedGraph.coord_mapCLM _ _ _ _ _ _ _ _ _ _ _ _ «hλ» j x

theorem second_apply (j : ℕ) (x : X A B W Q «λ») :
    second A B W Q «λ» x j =
      PairLp.second 1 (A j) W (WeightedGraph.coord _ _ (tilde A B W Q) «λ» j x) := by
  change PairLp.second 2 (B j) W (WeightedGraph.output _ _ (tilde A B W Q) «λ» x j) = _
  rw [← WeightedGraph.coord_output _ _ _ _ «hλ» j x]
  exact second_tilde A B W Q j _

def leftCoords (j : ℕ) : Y A B Q «λ» →L[ℝ] Domain A W j :=
  (PairLp.left 1 (A j) W).comp (WeightedGraph.coord A B Q «λ» j)

include «hλ» in
theorem left_admissible (y : Y A B Q «λ») :
    WeightedGraph.Admissible (Domain A W) (Codomain B W) (tilde A B W Q) «λ»
      (fun j => leftCoords A B W Q «λ» j y) := by
  have hy := WeightedGraph.coordinates_admissible A B Q «λ» «hλ» y
  constructor
  · simpa only [leftCoords, ContinuousLinearMap.comp_apply, PairLp.norm_left] using hy.1
  · simpa only [leftCoords, ContinuousLinearMap.comp_apply, tilde_left, PairLp.norm_left] using hy.2

theorem norm_of_leftCoords (y : Y A B Q «λ») :
    ‖WeightedGraph.ofCoordinates _ _ (tilde A B W Q) «λ» «hλ»
      (fun j => leftCoords A B W Q «λ» j y) (left_admissible A B W Q «λ» «hλ» y)‖ = ‖y‖ := by
  rw [WeightedGraph.norm_ofCoordinates]
  simp only [leftCoords, ContinuousLinearMap.comp_apply, tilde_left, PairLp.norm_left]
  exact (WeightedGraph.norm_formula A B Q «λ» «hλ» y).symm

def includeLeft : Y A B Q «λ» →L[ℝ] X A B W Q «λ» :=
  WeightedGraph.ofLinearCoordinates _ _ (tilde A B W Q) «λ» «hλ» (leftCoords A B W Q «λ»)
    (left_admissible A B W Q «λ» «hλ») 1
    (by intro y; rw [norm_of_leftCoords, one_mul])

@[simp] theorem coord_includeLeft (j : ℕ) (y : Y A B Q «λ») :
    WeightedGraph.coord _ _ (tilde A B W Q) «λ» j (includeLeft A B W Q «λ» «hλ» y) =
      PairLp.left 1 (A j) W (WeightedGraph.coord A B Q «λ» j y) :=
  WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ»
    (fun j => leftCoords A B W Q «λ» j y) (left_admissible A B W Q «λ» «hλ» y) j

@[simp] theorem norm_includeLeft (y : Y A B Q «λ») : ‖includeLeft A B W Q «λ» «hλ» y‖ = ‖y‖ :=
  norm_of_leftCoords A B W Q «λ» «hλ» y

def rightCoords (j : ℕ) : C0Sum (fun _ : ℕ => W) →L[ℝ] Domain A W j :=
  (PairLp.right 1 (A j) W).comp (C0Sum.evalCLM (fun _ : ℕ => W) j)

variable (hsum : Summable «λ») (hθ : (∑' j, «λ» j) ≤ 1)

include «hλ» hsum in
theorem right_weighted_summable (v : C0Sum (fun _ : ℕ => W)) :
    Summable (fun j => «λ» j * ‖v j‖) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg («hλ» j).le (norm_nonneg _))
  · intro j
    exact mul_le_mul_of_nonneg_left (v.norm_apply_le j) («hλ» j).le
  · exact hsum.mul_right ‖v‖

include «hλ» hsum hθ in
theorem right_weighted_le (v : C0Sum (fun _ : ℕ => W)) : (∑' j, «λ» j * ‖v j‖) ≤ ‖v‖ := by
  calc
    _ ≤ ∑' j, «λ» j * ‖v‖ :=
      (right_weighted_summable W «λ» «hλ» hsum v).tsum_le_tsum
        (fun j => mul_le_mul_of_nonneg_left (v.norm_apply_le j) («hλ» j).le) (hsum.mul_right ‖v‖)
    _ = (∑' j, «λ» j) * ‖v‖ := by rw [tsum_mul_right]
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hθ (norm_nonneg _)
    _ = ‖v‖ := one_mul _

include «hλ» hsum in
theorem right_admissible (v : C0Sum (fun _ : ℕ => W)) :
    WeightedGraph.Admissible (Domain A W) (Codomain B W) (tilde A B W Q) «λ»
      (fun j => rightCoords A W j v) := by
  constructor
  · simpa only [rightCoords, ContinuousLinearMap.comp_apply, C0Sum.evalCLM_apply, PairLp.norm_right]
      using right_weighted_summable W «λ» «hλ» hsum v
  · simpa only [rightCoords, ContinuousLinearMap.comp_apply, C0Sum.evalCLM_apply,
      tilde_right, PairLp.norm_right] using v.null_atTop

include hθ in
theorem norm_of_rightCoords (v : C0Sum (fun _ : ℕ => W)) :
    ‖WeightedGraph.ofCoordinates _ _ (tilde A B W Q) «λ» «hλ»
      (fun j => rightCoords A W j v) (right_admissible A B W Q «λ» «hλ» hsum v)‖ = ‖v‖ := by
  rw [WeightedGraph.norm_ofCoordinates]
  simp only [rightCoords, ContinuousLinearMap.comp_apply, C0Sum.evalCLM_apply,
    tilde_right, PairLp.norm_right]
  rw [← C0Sum.norm_eq_iSup v]
  exact max_eq_right (right_weighted_le W «λ» «hλ» hsum hθ v)

def includeRight : C0Sum (fun _ : ℕ => W) →L[ℝ] X A B W Q «λ» :=
  WeightedGraph.ofLinearCoordinates _ _ (tilde A B W Q) «λ» «hλ» (rightCoords A W)
    (right_admissible A B W Q «λ» «hλ» hsum) 1
    (by intro v; rw [norm_of_rightCoords A B W Q «λ» «hλ» hsum hθ, one_mul])

@[simp] theorem coord_includeRight (j : ℕ) (v : C0Sum (fun _ : ℕ => W)) :
    WeightedGraph.coord _ _ (tilde A B W Q) «λ» j (includeRight A B W Q «λ» «hλ» hsum hθ v) =
      PairLp.right 1 (A j) W (v j) := WeightedGraph.coord_ofCoordinates _ _ _ _ «hλ»
        (fun j => rightCoords A W j v) (right_admissible A B W Q «λ» «hλ» hsum v) j

@[simp] theorem norm_includeRight (v : C0Sum (fun _ : ℕ => W)) :
    ‖includeRight A B W Q «λ» «hλ» hsum hθ v‖ = ‖v‖ := norm_of_rightCoords A B W Q «λ» «hλ» hsum hθ v

theorem forget_includeLeft (y : Y A B Q «λ») :
    forget A B W Q «λ» (includeLeft A B W Q «λ» «hλ» y) = y := by
  apply WeightedGraph.coordinates_injective A B Q «λ» «hλ»
  intro j
  rw [coord_forget A B W Q «λ» «hλ», coord_includeLeft, PairLp.first_left]

theorem second_includeLeft (y : Y A B Q «λ») :
    second A B W Q «λ» (includeLeft A B W Q «λ» «hλ» y) = 0 := by
  apply C0Sum.ext
  intro j
  rw [second_apply A B W Q «λ» «hλ», coord_includeLeft, PairLp.second_left]
  rfl

theorem forget_includeRight (v : C0Sum (fun _ : ℕ => W)) :
    forget A B W Q «λ» (includeRight A B W Q «λ» «hλ» hsum hθ v) = 0 := by
  apply WeightedGraph.coordinates_injective A B Q «λ» «hλ»
  intro j
  rw [coord_forget A B W Q «λ» «hλ», coord_includeRight, PairLp.first_right, map_zero]

theorem second_includeRight (v : C0Sum (fun _ : ℕ => W)) :
    second A B W Q «λ» (includeRight A B W Q «λ» «hλ» hsum hθ v) = v := by
  apply C0Sum.ext
  intro j
  rw [second_apply A B W Q «λ» «hλ», coord_includeRight, PairLp.second_right]

theorem decomposition (x : X A B W Q «λ») :
    includeLeft A B W Q «λ» «hλ» (forget A B W Q «λ» x) +
      includeRight A B W Q «λ» «hλ» hsum hθ (second A B W Q «λ» x) = x := by
  apply WeightedGraph.coordinates_injective _ _ _ _ «hλ»
  intro j
  rw [map_add, coord_includeLeft, coord_includeRight, coord_forget A B W Q «λ» «hλ»,
    second_apply A B W Q «λ» «hλ»]
  exact PairLp.left_first_add_right_second 1 (A j) W _

def equiv : X A B W Q «λ» ≃L[ℝ] (Y A B Q «λ» × C0Sum (fun _ : ℕ => W)) where
  toLinearEquiv := {
    toFun := fun x => (forget A B W Q «λ» x, second A B W Q «λ» x)
    invFun := fun z => includeLeft A B W Q «λ» «hλ» z.1 + includeRight A B W Q «λ» «hλ» hsum hθ z.2
    left_inv := decomposition A B W Q «λ» «hλ» hsum hθ
    right_inv := by
      intro z
      apply Prod.ext
      · simp only [map_add, forget_includeLeft, forget_includeRight, add_zero]
      · simp only [map_add, second_includeLeft, second_includeRight, zero_add]
    map_add' := by intro x y; apply Prod.ext <;> exact map_add _ _ _
    map_smul' := by intro a x; apply Prod.ext <;> exact map_smul _ _ _ }
  continuous_toFun := (forget A B W Q «λ»).continuous.prodMk (second A B W Q «λ»).continuous
  continuous_invFun := ((includeLeft A B W Q «λ» «hλ»).continuous.comp continuous_fst).add
    ((includeRight A B W Q «λ» «hλ» hsum hθ).continuous.comp continuous_snd)

theorem norm_equiv_le (x : X A B W Q «λ») : ‖equiv A B W Q «λ» «hλ» hsum hθ x‖ ≤ ‖x‖ :=
  max_le (norm_forget_le A B W Q «λ» x) (norm_second_le A B W Q «λ» x)

theorem norm_le_two_mul_norm_equiv (x : X A B W Q «λ») :
    ‖x‖ ≤ 2 * ‖equiv A B W Q «λ» «hλ» hsum hθ x‖ := by
  have hx := norm_add_le (includeLeft A B W Q «λ» «hλ» (forget A B W Q «λ» x))
    (includeRight A B W Q «λ» «hλ» hsum hθ (second A B W Q «λ» x))
  rw [decomposition A B W Q «λ» «hλ» hsum hθ, norm_includeLeft, norm_includeRight] at hx
  change ‖x‖ ≤ 2 * max ‖forget A B W Q «λ» x‖ ‖second A B W Q «λ» x‖
  have h₁ := le_max_left ‖forget A B W Q «λ» x‖ ‖second A B W Q «λ» x‖
  have h₂ := le_max_right ‖forget A B W Q «λ» x‖ ‖second A B W Q «λ» x‖
  linarith

include «hλ» hsum hθ in
theorem isometric_complemented : ∃ (J : C0Sum (fun _ : ℕ => W) →L[ℝ] X A B W Q «λ»)
    (P : X A B W Q «λ» →L[ℝ] C0Sum (fun _ : ℕ => W)),
    (∀ v, ‖J v‖ = ‖v‖) ∧ ‖P‖ ≤ 1 ∧ P.comp J = ContinuousLinearMap.id ℝ _ := by
  refine ⟨includeRight A B W Q «λ» «hλ» hsum hθ, second A B W Q «λ», ?_, ?_, ?_⟩
  · exact norm_includeRight A B W Q «λ» «hλ» hsum hθ
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using norm_second_le A B W Q «λ» x
  · apply ContinuousLinearMap.ext
    intro v
    exact second_includeRight A B W Q «λ» «hλ» hsum hθ v

end GraphSplitting
end BanachGeometry
