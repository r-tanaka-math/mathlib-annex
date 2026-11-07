import BanachGeometry.OperatorGraphs.GraphAdmissible
import BanachGeometry.SequenceSpaces.C0Linear
import BanachGeometry.SequenceSpaces.L1Linear

/-! Contractive intertwining maps of the actual closed weighted graphs, and
linear coordinate constructors. No graph norm is replaced. -/

noncomputable section
namespace BanachGeometry
namespace WeightedGraph
variable (A B C D : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    [∀ j, NormedAddCommGroup (C j)] [∀ j, NormedSpace ℝ (C j)]
    [∀ j, NormedAddCommGroup (D j)] [∀ j, NormedSpace ℝ (D j)]
    (Q : ∀ j, A j →L[ℝ] B j) (R : ∀ j, C j →L[ℝ] D j) («λ» : ℕ → ℝ)
    (U : ∀ j, A j →L[ℝ] C j) (W : ∀ j, B j →L[ℝ] D j)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hW : ∀ j, ‖W j‖ ≤ 1)
    (hcomm : ∀ j, (R j).comp (U j) = (W j).comp (Q j))

def map (x : Space A B Q «λ») : Space C D R «λ» :=
  ⟨(L1Linear.continuousLinearMap U 1 hU x.1.1,
    C0Linear.continuousLinearMap W 1 zero_le_one hW x.1.2), by
    intro j
    change R j (U j (x.1.1 j)) = «λ» j • W j (x.1.2 j)
    have heq := congrArg (fun f : A j →L[ℝ] D j => f (x.1.1 j)) (hcomm j)
    change R j (U j (x.1.1 j)) = W j (Q j (x.1.1 j)) at heq
    rw [heq, x.2 j, map_smul]⟩

theorem norm_map_le (x : Space A B Q «λ») : ‖map A B C D Q R «λ» U W hU hW hcomm x‖ ≤ ‖x‖ := by
  change max ‖L1Linear.continuousLinearMap U 1 hU x.1.1‖
    ‖C0Linear.continuousLinearMap W 1 zero_le_one hW x.1.2‖ ≤ max ‖x.1.1‖ ‖x.1.2‖
  apply max_le_max
  · change ‖L1Linear.map U 1 hU x.1.1‖ ≤ ‖x.1.1‖
    simpa only [one_mul] using L1Linear.norm_map_le U 1 hU x.1.1
  · change ‖C0Linear.map W 1 zero_le_one hW x.1.2‖ ≤ ‖x.1.2‖
    simpa only [one_mul] using C0Linear.norm_map_le W 1 zero_le_one hW x.1.2

def mapCLM : Space A B Q «λ» →L[ℝ] Space C D R «λ» := by
  let f : Space A B Q «λ» →ₗ[ℝ] Space C D R «λ» :=
    { toFun := map A B C D Q R «λ» U W hU hW hcomm
      map_add' := by intro x y; apply Subtype.ext; apply Prod.ext <;> simp [map, map_add]
      map_smul' := by intro a x; apply Subtype.ext; apply Prod.ext <;> simp [map, map_smul] }
  refine ⟨f, AddMonoidHomClass.continuous_of_bound f 1 ?_⟩
  intro x
  change ‖map A B C D Q R «λ» U W hU hW hcomm x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using norm_map_le A B C D Q R «λ» U W hU hW hcomm x

theorem coord_mapCLM («hλ» : ∀ j, 0 < «λ» j) (j : ℕ) (x : Space A B Q «λ») :
    coord C D R «λ» j (mapCLM A B C D Q R «λ» U W hU hW hcomm x) = U j (coord A B Q «λ» j x) := by
  change («λ» j)⁻¹ • U j (x.1.1 j) = U j ((«λ» j)⁻¹ • x.1.1 j)
  exact ((U j).map_smul _ _).symm

end WeightedGraph

namespace WeightedGraph
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable (A B : ℕ → Type)
    [∀ j, NormedAddCommGroup (A j)] [∀ j, NormedSpace ℝ (A j)]
    [∀ j, NormedAddCommGroup (B j)] [∀ j, NormedSpace ℝ (B j)]
    (Q : ∀ j, A j →L[ℝ] B j) («λ» : ℕ → ℝ) («hλ» : ∀ j, 0 < «λ» j)

def ofLinearCoordinates (c : ∀ j, Z →L[ℝ] A j)
    (hc : ∀ z, Admissible A B Q «λ» (fun j => c j z)) (M : ℝ)
    (hbound : ∀ z, ‖ofCoordinates A B Q «λ» «hλ» (fun j => c j z) (hc z)‖ ≤ M * ‖z‖) :
    Z →L[ℝ] Space A B Q «λ» := by
  let f : Z →ₗ[ℝ] Space A B Q «λ» :=
    { toFun := fun z => ofCoordinates A B Q «λ» «hλ» (fun j => c j z) (hc z)
      map_add' := by
        intro x y; apply coordinates_injective A B Q «λ» «hλ»; intro j
        rw [map_add, coord_ofCoordinates, coord_ofCoordinates, coord_ofCoordinates, map_add]
      map_smul' := by
        intro a x; apply coordinates_injective A B Q «λ» «hλ»; intro j
        rw [map_smul, coord_ofCoordinates, coord_ofCoordinates, map_smul]
        rfl }
  exact ⟨f, AddMonoidHomClass.continuous_of_bound f M hbound⟩

@[simp] theorem coord_ofLinearCoordinates (c : ∀ j, Z →L[ℝ] A j)
    (hc : ∀ z, Admissible A B Q «λ» (fun j => c j z)) (M : ℝ)
    (hbound : ∀ z, ‖ofCoordinates A B Q «λ» «hλ» (fun j => c j z) (hc z)‖ ≤ M * ‖z‖)
    (z : Z) (j : ℕ) :
    coord A B Q «λ» j (ofLinearCoordinates A B Q «λ» «hλ» c hc M hbound z) = c j z :=
  coord_ofCoordinates A B Q «λ» «hλ» (fun j => c j z) (hc z) j

end WeightedGraph
end BanachGeometry
