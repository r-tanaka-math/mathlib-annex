import BanachGeometry.SequenceSpaces.C0Sum

/-!
# Homogeneous adapter and the separate extra branch

The homogeneous adapter is linear and isometric, so it respects the common
`ZeroAtInftyContinuousMap` boundary exactly. The Option adapter identifies one
extra branch plus a c₀ family with their heterogeneous c₀ sum. Its domain is
the ordinary product, carrying the maximum norm.
-/

noncomputable section
open Filter
namespace BanachGeometry

namespace C0Sum
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def toHomogeneous (x : C0Sum (fun _ : ℕ => V)) : ZeroAtInftyContinuousMap ℕ V where
  toFun := x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    simpa only [Filter.cocompact_eq_cofinite] using
      (tendsto_zero_iff_norm_tendsto_zero.2 x.null :
        Tendsto (fun n => x n) cofinite (nhds 0))

def ofHomogeneous (x : ZeroAtInftyContinuousMap ℕ V) : C0Sum (fun _ : ℕ => V) :=
  ofBound x (by
    have ht : Tendsto (fun n => x n) cofinite (nhds 0) := by
      simpa only [Filter.cocompact_eq_cofinite] using zero_at_infty x
    simpa using ht.norm) ‖x‖ (fun n => by
      calc
        ‖x n‖ = ‖x.toBCF n‖ := rfl
        _ ≤ ‖x.toBCF‖ := BoundedContinuousFunction.norm_coe_le_norm x.toBCF n
        _ = ‖x‖ := ZeroAtInftyContinuousMap.norm_toBCF_eq_norm)

/-- A coordinate-preserving linear isometry to the common homogeneous c₀ type. -/
def homogeneousLinearIsometryEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    C0Sum (fun _ : ℕ => V) ≃ₗᵢ[ℝ] ZeroAtInftyContinuousMap ℕ V where
  toFun := toHomogeneous
  invFun := ofHomogeneous
  left_inv x := by apply C0Sum.ext; intro n; rfl
  right_inv x := by apply ZeroAtInftyContinuousMap.ext; intro n; rfl
  map_add' x y := by apply ZeroAtInftyContinuousMap.ext; intro n; rfl
  map_smul' a x := by apply ZeroAtInftyContinuousMap.ext; intro n; rfl
  norm_map' x := by
    apply le_antisymm
    · change ‖(toHomogeneous x).toBCF‖ ≤ ‖x‖
      exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 x.norm_apply_le
    · apply C0Sum.norm_le (norm_nonneg _)
      intro n
      exact BoundedContinuousFunction.norm_coe_le_norm (toHomogeneous x).toBCF n

end C0Sum

universe u

def OptionFiber (E : Type u) (V : ℕ → Type u) : Option ℕ → Type u
  | none => E
  | some n => V n

instance optionFiberNormed (E : Type u) (V : ℕ → Type u)
    [NormedAddCommGroup E] [∀ n, NormedAddCommGroup (V n)] (i : Option ℕ) :
    NormedAddCommGroup (OptionFiber E V i) :=
  match i with
  | none => inferInstanceAs (NormedAddCommGroup E)
  | some n => inferInstanceAs (NormedAddCommGroup (V n))

instance optionFiberNormedSpace (E : Type u) (V : ℕ → Type u)
    [NormedAddCommGroup E] [∀ n, NormedAddCommGroup (V n)]
    [NormedSpace ℝ E] [∀ n, NormedSpace ℝ (V n)] (i : Option ℕ) :
    NormedSpace ℝ (OptionFiber E V i) :=
  match i with
  | none => inferInstanceAs (NormedSpace ℝ E)
  | some n => inferInstanceAs (NormedSpace ℝ (V n))

/-- A single exceptional Option coordinate does not affect a cofinite limit. -/
theorem tendsto_option_of_some {f : Option ℕ → ℝ}
    (h : Tendsto (fun n => f (some n)) cofinite (nhds 0)) :
    Tendsto f cofinite (nhds 0) := by
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  have hfin : {n : ℕ | f (some n) ∉ s}.Finite := mem_cofinite.1 (h s hs)
  apply mem_cofinite.2
  apply ((Set.finite_singleton none).union (hfin.image (@Option.some ℕ))).subset
  intro i hi
  cases i with
  | none => exact Or.inl (by simp)
  | some n => exact Or.inr ⟨n, hi, rfl⟩

section OptionAdapter
variable (E : Type u) (V : ℕ → Type u)
    [NormedAddCommGroup E] [∀ n, NormedAddCommGroup (V n)]
    [NormedSpace ℝ E] [∀ n, NormedSpace ℝ (V n)]

def optionJoinRaw (x : E × C0Sum V) : ∀ i, OptionFiber E V i
  | none => x.1
  | some n => x.2 n

def optionJoin (x : E × C0Sum V) : C0Sum (OptionFiber E V) :=
  C0Sum.ofBound (optionJoinRaw E V x)
    (tendsto_option_of_some x.2.null) ‖x‖ (by
      intro i
      cases i with
      | none => exact norm_fst_le x
      | some n => exact (x.2.norm_apply_le n).trans (norm_snd_le x))

def optionSplit (x : C0Sum (OptionFiber E V)) : E × C0Sum V :=
  (x none, C0Sum.ofBound (fun n => x (some n))
    (x.null.comp (show Function.Injective (@Option.some ℕ) from
      fun _ _ h => Option.some.inj h).tendsto_cofinite) ‖x‖
    (fun n => x.norm_apply_le (some n)))

/-- The ∞ branch is a separate maximum-norm summand, not the first
integer coordinate and not an unrestricted countable ℓ∞ sum. -/
def optionLinearIsometryEquiv : (E × C0Sum V) ≃ₗᵢ[ℝ] C0Sum (OptionFiber E V) where
  toFun := optionJoin E V
  invFun := optionSplit E V
  left_inv x := by
    apply Prod.ext
    · rfl
    · apply C0Sum.ext; intro n; rfl
  right_inv x := by apply C0Sum.ext; intro i; cases i <;> rfl
  map_add' x y := by apply C0Sum.ext; intro i; cases i <;> rfl
  map_smul' a x := by apply C0Sum.ext; intro i; cases i <;> rfl
  norm_map' x := by
    apply le_antisymm
    · apply C0Sum.norm_le (norm_nonneg _)
      intro i
      cases i with
      | none => exact norm_fst_le x
      | some n => exact (x.2.norm_apply_le n).trans (norm_snd_le x)
    · change max ‖x.1‖ ‖x.2‖ ≤ ‖optionJoin E V x‖
      apply max_le
      · exact (optionJoin E V x).norm_apply_le none
      · apply C0Sum.norm_le (norm_nonneg _)
        intro n
        exact (optionJoin E V x).norm_apply_le (some n)

end OptionAdapter
end BanachGeometry
