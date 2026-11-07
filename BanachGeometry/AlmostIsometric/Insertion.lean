import BanachGeometry.AlmostIsometric.InsertionIndices
import BanachGeometry.AlmostIsometric.FixedSpaces

/-!
# R6 §3: insertion, inverse, outer c₀ membership, and both norm estimates

The extra branch is joined by a maximum-norm linear isometry and then
reindexed by `none ↦ N`, `some k ↦ k` (k<N), `some k ↦ k+1` (k≥N).
The row transformations use the actual A_N and B_k, not an untyped shift.

This is the metric portion of Theorem 3.1 under the explicit H1 data of
AlmostIsometricFamily. Complemented copies, coordinate splittings, finite-sum
exclusion and nonisomorphism are assembled in later modules, including
FamilyFromHilbertData, NoC0Closure and Existence.
-/

noncomputable section
namespace BanachGeometry
namespace AlmostIsometricFamily

variable (d : AlmostIsometricFamily)

abbrev Branch := OptionFiber d.ZInfty (fun k => d.Z k)

/-- The component equivalences used when the extra branch is inserted at N. -/
def insertionComponent (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (j : Option ℕ) :
    PointedBiLip (d.Branch j) (d.Z (branchIndexEquiv N j)) C := by
  cases j with
  | none => exact d.intoRow N C hC htail
  | some k =>
    by_cases hk : k < N
    · have hidx : branchIndexEquiv N (some k) = k := by
        change (if k < N then k else k + 1) = k
        exact if_pos hk
      exact Eq.mpr (congrArg (fun n : ℕ => PointedBiLip (d.Branch (some k)) (d.Z n) C) hidx)
        (PointedBiLip.refl (d.Z k) C hC)
    · have hidx : branchIndexEquiv N (some k) = k + 1 := by
        change (if k < N then k else k + 1) = k + 1
        exact if_neg hk
      exact Eq.mpr (congrArg (fun n : ℕ => PointedBiLip (d.Branch (some k)) (d.Z n) C) hidx)
        (d.rowStep k C hC (htail k (Nat.le_of_not_gt hk)))

def branchInsertion (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) :
    PointedBiLip (C0Sum d.Branch) d.FixedY C :=
  c0ReindexBiLip (fun k => d.Z k) (branchIndexEquiv N) C
    (le_trans (by norm_num) hC) (d.insertionComponent N C hC htail)

/-- The paper's f_N as an actual equivalence of the two fixed normed spaces.
Forward and inverse c₀ membership follow from `c0ReindexBiLip`. -/
def nearEquiv (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) : PointedBiLip d.FixedX d.FixedY C := by
  let j := optionLinearIsometryEquiv d.ZInfty (fun k => d.Z k)
  let b := d.branchInsertion N C hC htail
  refine { equiv := j.toEquiv.trans b.equiv, zero_eq := ?_, forward := ?_, backward := ?_ }
  · change b.equiv (j 0) = 0
    simpa using b.zero_eq
  · intro x y
    change ‖b.equiv (j x) - b.equiv (j y)‖ ≤ C * ‖x - y‖
    simpa only [← j.map_sub, j.norm_map] using b.forward (j x) (j y)
  · intro x y
    change ‖j.symm (b.equiv.symm x) - j.symm (b.equiv.symm y)‖ ≤ C * ‖x - y‖
    simpa only [← j.symm.map_sub, j.symm.norm_map] using b.backward x y

/-- The inserted coordinate is the whole A_N image of the extra branch. -/
theorem nearEquiv_at_inserted (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (x : d.FixedX) :
    (d.nearEquiv N C hC htail).equiv x N = (d.intoRow N C hC htail).equiv x.1 := by
  exact c0ReindexBiLip_apply_index (fun k => d.Z k) (branchIndexEquiv N) C
    (le_trans (by norm_num) hC) (d.insertionComponent N C hC htail)
    (optionJoin d.ZInfty (fun k => d.Z k) x) none

/-- Old branch k is evaluated at its insertion-permutation position.
For k<N the component is the identity; for k≥N it is the actual B_k. -/
theorem nearEquiv_at_old_branch (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (x : d.FixedX) (k : ℕ) :
    (d.nearEquiv N C hC htail).equiv x (branchIndexEquiv N (some k)) =
      (d.insertionComponent N C hC htail (some k)).equiv (x.2 k) := by
  exact c0ReindexBiLip_apply_index (fun k => d.Z k) (branchIndexEquiv N) C
    (le_trans (by norm_num) hC) (d.insertionComponent N C hC htail)
    (optionJoin d.ZInfty (fun k => d.Z k) x) (some k)

/-- The extra inverse component is A_N⁻¹ w_N. -/
theorem nearEquiv_symm_extra (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (w : d.FixedY) :
    ((d.nearEquiv N C hC htail).equiv.symm w).1 =
      (d.intoRow N C hC htail).equiv.symm (w N) := by
  exact c0ReindexBiLip_symm_apply (fun k => d.Z k) (branchIndexEquiv N) C
    (le_trans (by norm_num) hC) (d.insertionComponent N C hC htail) w none

/-- The old inverse branch is read at k or k+1 and transformed by the
inverse component. This is the paper's inverse formula on the actual c₀ type. -/
theorem nearEquiv_symm_old_branch (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (w : d.FixedY) (k : ℕ) :
    ((d.nearEquiv N C hC htail).equiv.symm w).2 k =
      (d.insertionComponent N C hC htail (some k)).equiv.symm
        (w (branchIndexEquiv N (some k))) := by
  exact c0ReindexBiLip_symm_apply (fun k => d.Z k) (branchIndexEquiv N) C
    (le_trans (by norm_num) hC) (d.insertionComponent N C hC htail) w (some k)

/-- R6 §3, metric conclusion with fixed carrier types and fixed norms.
This theorem is stated for normed spaces. SequenceSpaces.C0Banach and
L1Separable supply completeness and separability for the Banach bundles
assembled in FixedBanach. -/
theorem fixed_spaces_almost_isometric (ε : ℝ) (hε : 0 < ε) :
    ∃ f : d.FixedX ≃ d.FixedY,
      f 0 = 0 ∧
      (∀ x x', ‖f x - f x'‖ ≤ (1 + ε) * ‖x - x'‖) ∧
      (∀ y y', ‖f.symm y - f.symm y'‖ ≤ (1 + ε) * ‖y - y'‖) := by
  obtain ⟨N, hN⟩ := d.exists_tail_bound ε hε
  let f := d.nearEquiv N (1 + ε) (by linarith) hN
  exact ⟨f.equiv, f.zero_eq, f.forward, f.backward⟩

end AlmostIsometricFamily
end BanachGeometry
