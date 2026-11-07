/- Concrete block-by-block enumeration of nonempty finite fibres.
The inverse also has a located-block formula, not a filler-coordinate enumeration.
Local execution status is recorded in the external qualification receipts. -/
import BanachGeometry.HilbertSums.ScaleClock.Growth

noncomputable section
namespace BanachGeometry.HilbertSums.Nonlinear.FiniteFibres
variable (A : ℕ → Type*) [∀ n, Fintype (A n)] [∀ n, Nonempty (A n)]

def offset : ℕ → ℕ
  | 0 => 0
  | n + 1 => offset n + Fintype.card (A n)

@[simp] theorem offset_zero : offset A 0 = 0 := rfl
@[simp] theorem offset_succ (n : ℕ) : offset A (n + 1) = offset A n + Fintype.card (A n) := rfl

theorem card_pos (n : ℕ) : 0 < Fintype.card (A n) := Fintype.card_pos_iff.mpr inferInstance

theorem offset_strictMono : StrictMono (offset A) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [offset_succ]
  exact Nat.lt_add_of_pos_right (card_pos A n)

theorem le_offset (n : ℕ) : n ≤ offset A n := by
  induction n with
  | zero => simp
  | succ n ih => rw [offset_succ]; have h := card_pos A n; omega

def rank (a : Σ n, A n) : ℕ := offset A a.1 + (Fintype.equivFin (A a.1) a.2).val

theorem rank_lower (a : Σ n, A n) : offset A a.1 ≤ rank A a := Nat.le_add_right _ _

theorem rank_upper (a : Σ n, A n) : rank A a < offset A (a.1 + 1) := by
  rw [offset_succ]
  exact Nat.add_lt_add_left (Fintype.equivFin (A a.1) a.2).isLt _

theorem rank_injective : Function.Injective (rank A) := by
  classical
  rintro ⟨n, a⟩ ⟨m, b⟩ hab
  have hnm : n = m := by
    rcases lt_trichotomy n m with h | h | h
    · have h1 := rank_upper A ⟨n, a⟩
      have h2 := (offset_strictMono A).monotone (show n + 1 ≤ m by omega)
      have h3 := rank_lower A ⟨m, b⟩
      change rank A ⟨n, a⟩ < offset A (n + 1) at h1
      change offset A m ≤ rank A ⟨m, b⟩ at h3
      omega
    · exact h
    · have h1 := rank_upper A ⟨m, b⟩
      have h2 := (offset_strictMono A).monotone (show m + 1 ≤ n by omega)
      have h3 := rank_lower A ⟨n, a⟩
      change rank A ⟨m, b⟩ < offset A (m + 1) at h1
      change offset A n ≤ rank A ⟨n, a⟩ at h3
      omega
  subst m
  have hval : (Fintype.equivFin (A n) a).val = (Fintype.equivFin (A n) b).val := by
    simpa only [rank, Nat.add_left_cancel_iff] using hab
  have he : a = b := (Fintype.equivFin (A n)).injective (Fin.ext hval)
  subst b
  rfl

theorem exists_offset_upper (j : ℕ) : ∃ n, j < offset A (n + 1) := by
  exact ⟨j, (Nat.lt_succ_self j).trans_le (le_offset A (j + 1))⟩

def locate (j : ℕ) : ℕ := Nat.find (exists_offset_upper A j)

theorem locate_upper (j : ℕ) : j < offset A (locate A j + 1) :=
  Nat.find_spec (exists_offset_upper A j)

theorem locate_lower (j : ℕ) : offset A (locate A j) ≤ j := by
  by_cases hzero : locate A j = 0
  · simp [hzero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    by_contra h
    have hpred : j < offset A (n + 1) := by simpa only [hn] using lt_of_not_ge h
    have hmin : locate A j ≤ n := Nat.find_min' (exists_offset_upper A j) hpred
    omega

/-- Locate the unique block, then use its finite-coordinate equivalence. -/
def locatedCoordinate (j : ℕ) : Σ n, A n :=
  ⟨locate A j, (Fintype.equivFin (A (locate A j))).symm
    ⟨j - offset A (locate A j), by
      have hu := locate_upper A j
      have hl := locate_lower A j
      rw [offset_succ] at hu
      omega⟩⟩

theorem rank_locatedCoordinate (j : ℕ) : rank A (locatedCoordinate A j) = j := by
  let n := locate A j
  let k : Fin (Fintype.card (A n)) := ⟨j - offset A n, by
    have hu := locate_upper A j
    have hl := locate_lower A j
    rw [offset_succ] at hu
    dsimp [n]
    omega⟩
  change offset A n + (Fintype.equivFin (A n) ((Fintype.equivFin (A n)).symm k)).val = j
  rw [(Fintype.equivFin (A n)).apply_symm_apply]
  exact Nat.add_sub_of_le (locate_lower A j)

theorem rank_surjective : Function.Surjective (rank A) :=
  fun j => ⟨locatedCoordinate A j, rank_locatedCoordinate A j⟩

def enumeration : ℕ ≃ (Σ n, A n) :=
  (Equiv.ofBijective (rank A) ⟨rank_injective A, rank_surjective A⟩).symm

@[simp] theorem rank_enumeration (j : ℕ) : rank A (enumeration A j) = j :=
  (Equiv.ofBijective (rank A) ⟨rank_injective A, rank_surjective A⟩).apply_symm_apply j

theorem enumeration_eq_located (j : ℕ) : enumeration A j = locatedCoordinate A j := by
  apply rank_injective A
  rw [rank_enumeration, rank_locatedCoordinate]

/-- The jth scalar coordinate belongs to block at most j (zero based). -/
theorem enumeration_block_le (j : ℕ) : (enumeration A j).1 ≤ j := by
  have h1 := le_offset A (enumeration A j).1
  have h2 := rank_lower A (enumeration A j)
  rw [rank_enumeration] at h2
  omega

end BanachGeometry.HilbertSums.Nonlinear.FiniteFibres
