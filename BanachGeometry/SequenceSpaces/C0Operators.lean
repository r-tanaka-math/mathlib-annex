import BanachGeometry.SequenceSpaces.C0Banach

/-! Bounded evaluation and finite-head projections on the retained c₀ norm. -/

noncomputable section
namespace BanachGeometry
namespace C0Sum
variable (V : ℕ → Type*) [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)]

def evalCLM (i : ℕ) : C0Sum V →L[ℝ] V i :=
  ({ toFun := fun x => x i
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : C0Sum V →ₗ[ℝ] V i).mkContinuous 1
    (fun x => by
      change ‖x i‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using x.norm_apply_le i)

@[simp] theorem evalCLM_apply (i : ℕ) (x : C0Sum V) : evalCLM V i x = x i := rfl

theorem norm_head_le (n : ℕ) (x : C0Sum V) : ‖head V n x‖ ≤ ‖x‖ := by
  apply C0Sum.norm_le (norm_nonneg _)
  intro i
  rw [head_apply]
  split_ifs
  · exact x.norm_apply_le i
  · simpa using norm_nonneg x

def headCLM (n : ℕ) : C0Sum V →L[ℝ] C0Sum V :=
  ({ toFun := head V n
     map_add' := by
       intro x y; apply C0Sum.ext; intro i
       simp only [head_apply, add_apply]
       split_ifs <;> simp
     map_smul' := by
       intro a x; apply C0Sum.ext; intro i
       simp only [head_apply, smul_apply]
       split_ifs <;> simp } : C0Sum V →ₗ[ℝ] C0Sum V).mkContinuous 1
    (fun x => by
      change ‖head V n x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_head_le V n x)

@[simp] theorem headCLM_apply (n : ℕ) (x : C0Sum V) : headCLM V n x = head V n x := rfl

def tailCLM (n : ℕ) : C0Sum V →L[ℝ] C0Sum V :=
  ContinuousLinearMap.id ℝ (C0Sum V) - headCLM V n

theorem tailCLM_apply_coord (n : ℕ) (x : C0Sum V) (i : ℕ) :
    tailCLM V n x i = if i < n then 0 else x i := by
  change x i - head V n x i = _
  rw [head_apply]
  split_ifs <;> simp

theorem norm_tailCLM_le (n : ℕ) (x : C0Sum V) : ‖tailCLM V n x‖ ≤ ‖x‖ := by
  apply C0Sum.norm_le (norm_nonneg _)
  intro i
  rw [tailCLM_apply_coord]
  split_ifs
  · simpa using norm_nonneg x
  · exact x.norm_apply_le i

theorem headCLM_idempotent (n : ℕ) :
    (headCLM V n).comp (headCLM V n) = headCLM V n := by
  apply ContinuousLinearMap.ext
  intro x
  apply C0Sum.ext; intro i
  simp only [ContinuousLinearMap.comp_apply, headCLM_apply, head_apply]
  split_ifs <;> rfl

def FiniteHead (n : ℕ) := LinearMap.range (headCLM V n).toLinearMap

theorem mem_finiteHead_iff (n : ℕ) (x : C0Sum V) :
    x ∈ FiniteHead V n ↔ ∀ i, n ≤ i → x i = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ i hi
    exact (head_apply V n y i).trans (if_neg (by omega))
  · intro hx
    refine ⟨x, ?_⟩
    apply C0Sum.ext; intro i
    change head V n x i = x i
    rw [head_apply]
    split_ifs with hi
    · rfl
    · exact (hx i (by omega)).symm

theorem isClosed_finiteHead (n : ℕ) : IsClosed (FiniteHead V n : Set (C0Sum V)) := by
  have heq : (FiniteHead V n : Set (C0Sum V)) = {x | headCLM V n x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact congrArg (fun f : C0Sum V →L[ℝ] C0Sum V => f y) (headCLM_idempotent V n)
    · intro hx; exact ⟨x, hx⟩
  rw [heq]
  exact isClosed_eq (headCLM V n).continuous continuous_id

instance finiteHeadComplete [∀ n, CompleteSpace (V n)] (n : ℕ) :
    CompleteSpace (FiniteHead V n) := (isClosed_finiteHead V n).isComplete.completeSpace_coe

end C0Sum
end BanachGeometry
