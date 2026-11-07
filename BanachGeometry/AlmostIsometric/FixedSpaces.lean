import BanachGeometry.SequenceSpaces.L1Map
import BanachGeometry.SequenceSpaces.C0Adapters

/-!
# R6 §3: fixed spaces, A_N, and B_k

All indices are zero based. Row k uses X_i for i<k, and Y_i for i≥k.
The transition k→k+1 changes exactly coordinate i=k, using ψ_i⁻¹.
No final tolerance occurs in the definitions of the spaces.
-/

noncomputable section
open Filter
namespace BanachGeometry

/-- Explicit H1 data only. H2--H4 and the analytic supply are not assumed
implicitly and are not asserted by the metric construction. -/
structure AlmostIsometricFamily where
  X : ℕ → SeparableRealBanach
  Y : ℕ → SeparableRealBanach
  bound : ℕ → ℝ
  one_le : ∀ i, 1 ≤ bound i
  tends_one : Tendsto bound atTop (nhds 1)
  psi : ∀ i, PointedBiLip (X i).Carrier (Y i).Carrier (bound i)

namespace AlmostIsometricFamily
variable (d : AlmostIsometricFamily)

def mixed (k i : ℕ) : SeparableRealBanach := if i < k then d.X i else d.Y i

abbrev ZInfty := L1Sum (fun i => (d.X i).Carrier)
abbrev Z (k : ℕ) := L1Sum (fun i => (d.mixed k i).Carrier)
abbrev FixedY := C0Sum (fun k => d.Z k)
abbrev FixedX := d.ZInfty × d.FixedY

/-- The head of row zero is empty. -/
@[simp] theorem mixed_zero (i : ℕ) : d.mixed 0 i = d.Y i := by simp [mixed]

theorem mixed_head (k i : ℕ) (h : i < k) : d.mixed k i = d.X i := by simp [mixed, h]

theorem mixed_tail (k i : ℕ) (h : k ≤ i) : d.mixed k i = d.Y i := by
  simp [mixed, Nat.not_lt.mpr h]

theorem fixedX_norm (x : d.FixedX) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl

theorem fixedY_null (x : d.FixedY) : Tendsto (fun k => ‖x k‖) atTop (nhds 0) :=
  x.null_atTop

theorem row_norm (k : ℕ) (x : d.Z k) : ‖x‖ = ∑' i, ‖x i‖ := l1_norm_eq_tsum x

/-- Coordinate map for A_N; `C` may be any upper bound for the tail constants. -/
def intoRowCoord (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) (i : ℕ) :
    PointedBiLip (d.X i).Carrier (d.mixed N i).Carrier C := by
  by_cases hi : i < N
  · exact Eq.mpr (congrArg (fun Z : SeparableRealBanach =>
      PointedBiLip (d.X i).Carrier Z.Carrier C) (d.mixed_head N i hi))
      (PointedBiLip.refl (d.X i).Carrier C hC)
  · exact Eq.mpr (congrArg (fun Z : SeparableRealBanach =>
      PointedBiLip (d.X i).Carrier Z.Carrier C)
        (d.mixed_tail N i (Nat.le_of_not_gt hi)))
      ((d.psi i).weaken (htail i (Nat.le_of_not_gt hi)))

/-- R6 A_N, with summability and its inverse supplied by `l1BiLip`. -/
def intoRow (N : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (htail : ∀ i, N ≤ i → d.bound i ≤ C) : PointedBiLip d.ZInfty (d.Z N) C :=
  l1BiLip C (d.intoRowCoord N C hC htail)

/-- Coordinate map for B_k. The changed coordinate is Y_k→X_k. -/
def rowStepCoord (k : ℕ) (C : ℝ) (hC : 1 ≤ C) (hk : d.bound k ≤ C) (i : ℕ) :
    PointedBiLip (d.mixed k i).Carrier (d.mixed (k + 1) i).Carrier C := by
  let P := fun U V : SeparableRealBanach => PointedBiLip U.Carrier V.Carrier C
  by_cases hi : i < k
  · exact Eq.mpr (congrArg₂ P (d.mixed_head k i hi)
      (d.mixed_head (k + 1) i (by omega))) (PointedBiLip.refl (d.X i).Carrier C hC)
  · by_cases he : i = k
    · subst i
      exact Eq.mpr (congrArg₂ P (d.mixed_tail k k le_rfl)
        (d.mixed_head (k + 1) k (by omega))) ((d.psi k).symm.weaken hk)
    · exact Eq.mpr (congrArg₂ P (d.mixed_tail k i (by omega))
        (d.mixed_tail (k + 1) i (by omega))) (PointedBiLip.refl (d.Y i).Carrier C hC)

/-- R6 B_k with the same two-sided bound C. -/
def rowStep (k : ℕ) (C : ℝ) (hC : 1 ≤ C) (hk : d.bound k ≤ C) :
    PointedBiLip (d.Z k) (d.Z (k + 1)) C :=
  l1BiLip C (d.rowStepCoord k C hC hk)

/-- A tolerance is used only to choose an index, never to redefine a space. -/
theorem exists_tail_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i, N ≤ i → d.bound i ≤ 1 + ε := by
  have he : ∀ᶠ i in atTop, d.bound i < 1 + ε :=
    d.tends_one.eventually (eventually_lt_nhds (by linarith : 1 < 1 + ε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 he
  exact ⟨N, fun i hi => (hN i hi).le⟩

end AlmostIsometricFamily
end BanachGeometry
