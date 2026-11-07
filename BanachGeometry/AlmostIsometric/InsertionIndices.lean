import BanachGeometry.AlmostIsometric.PointedBiLip

/-!
# Insertion of the extra branch at an arbitrary N, including N = 0

`none` is the separate ∞ branch. Ordinary branches have indices `some k`.
The map sends `none` to N, retains k<N, and sends k≥N to k+1.
-/

namespace BanachGeometry

def branchIndex (N : ℕ) : Option ℕ → ℕ
  | none => N
  | some k => if k < N then k else k + 1

def branchIndexInv (N k : ℕ) : Option ℕ :=
  if k < N then some k else if k = N then none else some (k - 1)

theorem branchIndex_left_inv (N : ℕ) (j : Option ℕ) :
    branchIndexInv N (branchIndex N j) = j := by
  cases j with
  | none => simp [branchIndex, branchIndexInv]
  | some k =>
    by_cases h : k < N
    · simp [branchIndex, branchIndexInv, h]
    · have h₁ : ¬ k + 1 < N := by omega
      have h₂ : k + 1 ≠ N := by omega
      simp [branchIndex, branchIndexInv, h, h₁, h₂]

theorem branchIndex_right_inv (N k : ℕ) :
    branchIndex N (branchIndexInv N k) = k := by
  by_cases h : k < N
  · simp [branchIndex, branchIndexInv, h]
  · by_cases he : k = N
    · subst k; simp [branchIndex, branchIndexInv]
    · have h₁ : ¬ k - 1 < N := by omega
      have h₂ : k - 1 + 1 = k := by omega
      simp [branchIndex, branchIndexInv, h, he, h₁, h₂]

def branchIndexEquiv (N : ℕ) : Option ℕ ≃ ℕ where
  toFun := branchIndex N
  invFun := branchIndexInv N
  left_inv := branchIndex_left_inv N
  right_inv := branchIndex_right_inv N

@[simp] theorem branchIndexEquiv_none (N : ℕ) : branchIndexEquiv N none = N := rfl

theorem branchIndexEquiv_some_lt (N k : ℕ) (h : k < N) :
    branchIndexEquiv N (some k) = k := by simp [branchIndexEquiv, branchIndex, h]

theorem branchIndexEquiv_some_ge (N k : ℕ) (h : N ≤ k) :
    branchIndexEquiv N (some k) = k + 1 := by
  simp [branchIndexEquiv, branchIndex, Nat.not_lt.mpr h]

@[simp] theorem branchIndexEquiv_zero_some (k : ℕ) :
    branchIndexEquiv 0 (some k) = k + 1 := by simp [branchIndexEquiv, branchIndex]

theorem branchIndexEquiv_symm_at (N : ℕ) : (branchIndexEquiv N).symm N = none := by
  exact (branchIndexEquiv N).symm_apply_apply none

theorem branchIndexEquiv_symm_lt (N k : ℕ) (h : k < N) :
    (branchIndexEquiv N).symm k = some k := by
  simp [branchIndexEquiv, branchIndexInv, h]

theorem branchIndexEquiv_symm_succ (N k : ℕ) (h : N ≤ k) :
    (branchIndexEquiv N).symm (k + 1) = some k := by
  have h₁ : ¬ k + 1 < N := by omega
  have h₂ : k + 1 ≠ N := by omega
  simp [branchIndexEquiv, branchIndexInv, h₁, h₂]

end BanachGeometry
