import BanachGeometry.SequenceSpaces.SumFinite
import BanachGeometry.NoC0.L1NoC0Reduction
import Mathlib.Logic.Equiv.Fin.Basic

/-! R6 Proposition 6.2: explicit finite graph rearrangement. The same
permutation moves spaces, maps, and weights. Finite products keep the max
norm, flattened graphs keep the original ℓ₁/max norm. For q>0 the bounds
are 1 and q. The no-copy corollary handles q=0 separately, so repetitions
and empty families are retained. No uniform bound on Q is assumed.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
namespace BanachGeometry
namespace FiniteGraph
variable {q : ℕ} (A B : Fin q → ℕ → Type)
    [∀ r j, NormedAddCommGroup (A r j)] [∀ r j, NormedSpace ℝ (A r j)]
    [∀ r j, NormedAddCommGroup (B r j)] [∀ r j, NormedSpace ℝ (B r j)]
    (Q : ∀ r j, A r j →L[ℝ] B r j) («λ» : Fin q → ℕ → ℝ)
    (e : ℕ ≃ Fin q × ℕ)

abbrev Rows := ∀ r, WeightedGraph.Space (A r) (B r) (Q r) («λ» r)
abbrev Flat := WeightedGraph.Space (fun n => A (e n).1 (e n).2)
  (fun n => B (e n).1 (e n).2) (fun n => Q (e n).1 (e n).2) (fun n => «λ» (e n).1 (e n).2)

def forward (u : Rows A B Q «λ») : Flat A B Q «λ» e :=
  ⟨((SumReindex.l1 (SumFinite.Total A) e).symm
      (SumFinite.l1Collect A (fun r => (u r).1.1)),
    (SumReindex.c0 (SumFinite.Total B) e).symm
      (SumFinite.c0Collect B (fun r => (u r).1.2))), by
    intro n
    simp only [SumReindex.l1_symm_apply, SumReindex.c0_symm_apply]
    exact (u (e n).1).2 (e n).2⟩

theorem reindexed_constraint (z : Flat A B Q «λ» e) (p : Fin q × ℕ) :
    Q p.1 p.2 ((SumReindex.l1 (SumFinite.Total A) e) z.1.1 p) =
      «λ» p.1 p.2 • ((SumReindex.c0 (SumFinite.Total B) e) z.1.2 p) := by
  obtain ⟨n,rfl⟩ := e.surjective p
  simpa only [SumReindex.l1_apply_index, SumReindex.c0_apply_index] using z.2 n

def backward (z : Flat A B Q «λ» e) : Rows A B Q «λ» := fun r =>
  ⟨(SumFinite.l1Row A r ((SumReindex.l1 (SumFinite.Total A) e) z.1.1),
    SumFinite.c0Row B r ((SumReindex.c0 (SumFinite.Total B) e) z.1.2)), by
    intro j
    exact reindexed_constraint A B Q «λ» e z (r,j)⟩

theorem backward_forward (u : Rows A B Q «λ») : backward A B Q «λ» e (forward A B Q «λ» e u) = u := by
  funext r
  apply Subtype.ext
  apply Prod.ext
  · change SumFinite.l1Row A r ((SumReindex.l1 (SumFinite.Total A) e)
      ((SumReindex.l1 (SumFinite.Total A) e).symm _)) = _
    rw [LinearIsometryEquiv.apply_symm_apply, SumFinite.l1Row_collect]
  · change SumFinite.c0Row B r ((SumReindex.c0 (SumFinite.Total B) e)
      ((SumReindex.c0 (SumFinite.Total B) e).symm _)) = _
    rw [LinearIsometryEquiv.apply_symm_apply, SumFinite.c0Row_collect]

theorem forward_backward (z : Flat A B Q «λ» e) : forward A B Q «λ» e (backward A B Q «λ» e z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · change (SumReindex.l1 (SumFinite.Total A) e).symm
      (SumFinite.l1Collect A (fun r => SumFinite.l1Row A r _)) = z.1.1
    rw [SumFinite.l1Collect_rows, LinearIsometryEquiv.symm_apply_apply]
  · change (SumReindex.c0 (SumFinite.Total B) e).symm
      (SumFinite.c0Collect B (fun r => SumFinite.c0Row B r _)) = z.1.2
    rw [SumFinite.c0Collect_rows, LinearIsometryEquiv.symm_apply_apply]

theorem norm_backward_le (z : Flat A B Q «λ» e) : ‖backward A B Q «λ» e z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro r
  change max ‖SumFinite.l1Row A r _‖ ‖SumFinite.c0Row B r _‖ ≤ max ‖z.1.1‖ ‖z.1.2‖
  apply max_le
  · apply (SumFinite.norm_l1Row_le A r _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact le_max_left _ _
  · apply (SumFinite.norm_c0Row_le B r _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact le_max_right _ _

theorem norm_forward_le (hq : 0 < q) (u : Rows A B Q «λ») :
    ‖forward A B Q «λ» e u‖ ≤ (q : ℝ) * ‖u‖ := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hfirst : ‖(fun r => (u r).1.1)‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro r; exact (norm_fst_le (u r).1).trans (norm_le_pi_norm u r)
  have hsecond : ‖(fun r => (u r).1.2)‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro r; exact (norm_snd_le (u r).1).trans (norm_le_pi_norm u r)
  change max ‖(SumReindex.l1 (SumFinite.Total A) e).symm _‖
    ‖(SumReindex.c0 (SumFinite.Total B) e).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  apply max_le
  · exact (SumFinite.norm_l1Collect_le A _).trans
      (mul_le_mul_of_nonneg_left hfirst (by positivity))
  · exact (SumFinite.norm_c0Collect_le B _).trans
      (hsecond.trans (by nlinarith [norm_nonneg u]))

def forwardCLM (hq : 0 < q) : Rows A B Q «λ» →L[ℝ] Flat A B Q «λ» e := by
  let f : Rows A B Q «λ» →ₗ[ℝ] Flat A B Q «λ» e :=
    { toFun := forward A B Q «λ» e
      map_add' := by
        intro u v; apply Subtype.ext; apply Prod.ext
        · apply lp.ext; funext n; rfl
        · apply C0Sum.ext; intro n; rfl
      map_smul' := by
        intro a u; apply Subtype.ext; apply Prod.ext
        · apply lp.ext; funext n; rfl
        · apply C0Sum.ext; intro n; rfl }
  refine ⟨f, AddMonoidHomClass.continuous_of_bound f q ?_⟩
  intro u
  change ‖forward A B Q «λ» e u‖ ≤ (q : ℝ) * ‖u‖
  exact norm_forward_le A B Q «λ» e hq u

def backwardCLM : Flat A B Q «λ» e →L[ℝ] Rows A B Q «λ» := by
  let f : Flat A B Q «λ» e →ₗ[ℝ] Rows A B Q «λ» :=
    { toFun := backward A B Q «λ» e
      map_add' := by
        intro z w; funext r; apply Subtype.ext; apply Prod.ext
        · change (SumFinite.l1RowCLM A r) ((SumReindex.l1 (SumFinite.Total A) e) (z.1.1 + w.1.1)) =
            (SumFinite.l1RowCLM A r) ((SumReindex.l1 (SumFinite.Total A) e) z.1.1) +
            (SumFinite.l1RowCLM A r) ((SumReindex.l1 (SumFinite.Total A) e) w.1.1)
          rw [map_add, map_add]
        · change (SumFinite.c0RowCLM B r) ((SumReindex.c0 (SumFinite.Total B) e) (z.1.2 + w.1.2)) =
            (SumFinite.c0RowCLM B r) ((SumReindex.c0 (SumFinite.Total B) e) z.1.2) +
            (SumFinite.c0RowCLM B r) ((SumReindex.c0 (SumFinite.Total B) e) w.1.2)
          rw [map_add, map_add]
      map_smul' := by
        intro a z; funext r; apply Subtype.ext; apply Prod.ext
        · change (SumFinite.l1RowCLM A r) ((SumReindex.l1 (SumFinite.Total A) e) (a • z.1.1)) =
            a • (SumFinite.l1RowCLM A r) ((SumReindex.l1 (SumFinite.Total A) e) z.1.1)
          rw [map_smul, map_smul]
        · change (SumFinite.c0RowCLM B r) ((SumReindex.c0 (SumFinite.Total B) e) (a • z.1.2)) =
            a • (SumFinite.c0RowCLM B r) ((SumReindex.c0 (SumFinite.Total B) e) z.1.2)
          rw [map_smul, map_smul] }
  refine ⟨f, AddMonoidHomClass.continuous_of_bound f 1 ?_⟩
  intro z
  change ‖backward A B Q «λ» e z‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using norm_backward_le A B Q «λ» e z

def equiv (hq : 0 < q) : Rows A B Q «λ» ≃L[ℝ] Flat A B Q «λ» e where
  toLinearEquiv :=
    { toFun := forward A B Q «λ» e
      invFun := backward A B Q «λ» e
      left_inv := backward_forward A B Q «λ» e
      right_inv := forward_backward A B Q «λ» e
      map_add' := (forwardCLM A B Q «λ» e hq).map_add
      map_smul' := (forwardCLM A B Q «λ» e hq).map_smul }
  continuous_toFun := (forwardCLM A B Q «λ» e hq).continuous
  continuous_invFun := (backwardCLM A B Q «λ» e).continuous

theorem norm_le_forward (u : Rows A B Q «λ») : ‖u‖ ≤ ‖forward A B Q «λ» e u‖ := by
  simpa only [backward_forward] using norm_backward_le A B Q «λ» e (forward A B Q «λ» e u)

end FiniteGraph

namespace WeightedGraph

/-- Finite graph products under the explicit BP-basis consequence. No
injectivity of the family indices is needed, and q=0 is included. -/
theorem finite_no_c0L2_of_basisDecay (q : ℕ) (A B : Fin q → ℕ → Type)
    [∀ r j, NormedAddCommGroup (A r j)] [∀ r j, NormedSpace ℝ (A r j)]
    [∀ r j, NormedAddCommGroup (B r j)] [∀ r j, NormedSpace ℝ (B r j)]
    (Q : ∀ r j, A r j →L[ℝ] B r j) («λ» : Fin q → ℕ → ℝ)
    («hλ» : ∀ r j, 0 < «λ» r j) (hQ : ∀ r j, CompletelyContinuous (Q r j))
    (hdecay : ∀ r j, BasisDecay (A r j)) :
    ¬ ContainsLinearCopy C0L2 (∀ r, Space (A r) (B r) (Q r) («λ» r)) := by
  cases q with
  | zero =>
    rintro ⟨T,b,hb,hT⟩
    let x := CanonicalSequences.column 0 (CanonicalSequences.l2Basis 0)
    have hx : ‖x‖ = 1 := by rw [LinearIsometry.norm_map, CanonicalSequences.norm_l2Basis]
    have hzero : T x = 0 := Subsingleton.elim _ _
    have he := hT x
    rw [hx,hzero,norm_zero,mul_one] at he
    exact (not_le_of_gt hb) he
  | succ q =>
    let e : ℕ ≃ Fin (q+1) × ℕ := (Nat.divModEquiv (q+1)).trans (Equiv.prodComm _ _)
    have hno := no_c0L2_of_coordinate_basisDecay
      (fun n => A (e n).1 (e n).2) (fun n => B (e n).1 (e n).2)
      (fun n => Q (e n).1 (e n).2) (fun n => «λ» (e n).1 (e n).2)
      (fun n => «hλ» (e n).1 (e n).2) (fun n => hQ (e n).1 (e n).2)
      (fun n => hdecay (e n).1 (e n).2)
    rintro ⟨T,b,hb,hT⟩
    apply hno
    let F := FiniteGraph.forwardCLM A B Q «λ» e (Nat.succ_pos q)
    refine ⟨F.comp T,b,hb,?_⟩
    intro x
    exact (hT x).trans (FiniteGraph.norm_le_forward A B Q «λ» e (T x))

end WeightedGraph
end BanachGeometry
