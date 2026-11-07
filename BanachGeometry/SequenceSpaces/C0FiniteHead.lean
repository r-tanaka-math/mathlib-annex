import BanachGeometry.SequenceSpaces.C0Operators
import Mathlib.Analysis.Normed.Group.Constructions

/-! The inherited finite head is exactly the finite maximum-norm product,
including n=0. No replacement of the outer fixed norm.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace C0Sum
variable (V : ℕ → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

-- These are aliases of the inherited submodule structures, fixing one path
-- for the finite-head equivalence and its normed dual consumers.
instance finiteHeadNormedGroup (n : ℕ) : NormedAddCommGroup (FiniteHead V n) :=
  (FiniteHead V n).normedAddCommGroup

instance finiteHeadNormedSpace (n : ℕ) : NormedSpace ℝ (FiniteHead V n) :=
  (FiniteHead V n).normedSpace

def finiteHeadToPi (n : ℕ) : FiniteHead V n →L[ℝ] (∀ r : Fin n, V r.val) where
  toFun x r := x.1 r.val
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_pi (fun r => (evalCLM V r.val).continuous.comp continuous_subtype_val)

def finiteHeadFromPi (n : ℕ) (z : ∀ r : Fin n, V r.val) : FiniteHead V n := by
  let f : ∀ i, V i := fun i => if hi : i < n then z ⟨i, hi⟩ else 0
  have hf : Tendsto (fun i => ‖f i‖) cofinite (nhds 0) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) cofinite (nhds 0)).congr'
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop n] with i hi
    simp only [f, dif_neg (Nat.not_lt.mpr hi), norm_zero]
  let x := ofBound f hf ‖z‖ (by
    intro i
    dsimp [f]
    split_ifs with hi
    · exact norm_le_pi_norm z ⟨i, hi⟩
    · simpa only [norm_zero] using (norm_nonneg z))
  refine ⟨x, (mem_finiteHead_iff V n x).mpr ?_⟩
  intro i hi
  change f i = 0
  simp only [f, dif_neg (Nat.not_lt.mpr hi)]

@[simp] theorem finiteHeadFromPi_apply (n : ℕ) (z : ∀ r : Fin n, V r.val) (i : ℕ) :
    (finiteHeadFromPi V n z).1 i = if hi : i < n then z ⟨i, hi⟩ else 0 := rfl

def finiteHeadEquivPi (n : ℕ) : FiniteHead V n ≃ₗᵢ[ℝ] (∀ r : Fin n, V r.val) where
  toFun := finiteHeadToPi V n
  invFun := finiteHeadFromPi V n
  left_inv x := by
    apply Subtype.ext
    apply C0Sum.ext
    intro i
    rw [finiteHeadFromPi_apply]
    split_ifs with hi
    · rfl
    · exact ((mem_finiteHead_iff V n x.1).mp x.2 i (Nat.le_of_not_gt hi)).symm
  right_inv z := by
    funext r
    change (finiteHeadFromPi V n z).1 r.val = z r
    rw [finiteHeadFromPi_apply, dif_pos r.isLt]
  map_add' := (finiteHeadToPi V n).map_add
  map_smul' := (finiteHeadToPi V n).map_smul
  norm_map' x := by
    change ‖finiteHeadToPi V n x‖ = ‖(x.1 : C0Sum V)‖
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro r
      exact x.1.norm_apply_le r.val
    · apply C0Sum.norm_le (norm_nonneg _)
      intro i
      change ‖x.1 i‖ ≤ ‖finiteHeadToPi V n x‖
      by_cases hi : i < n
      · exact norm_le_pi_norm (finiteHeadToPi V n x) ⟨i,hi⟩
      · rw [(mem_finiteHead_iff V n x.1).mp x.2 i (Nat.le_of_not_gt hi), norm_zero]
        exact norm_nonneg _

end C0Sum
end BanachGeometry
