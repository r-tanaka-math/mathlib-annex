import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.SetTheory.Cardinal.Basic

/-!
# A self-embedding missing any given finite subset

C06, UNBUILT. This is an explicit shift on an embedded copy of ℕ, followed
by finite induction. It does not assume that the entire index type is
countable and it does not assume an unproved Hilbert-space isomorphism.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace MathlibAnnex.FiniteCentral
universe u
variable {ι : Type u}

private def shiftAlong (f : ℕ ↪ ι) (x : ι) : ι :=
  if h : ∃ n, f n = x then f (Nat.find h + 1) else x

private theorem shiftAlong_on (f : ℕ ↪ ι) (n : ℕ) :
    shiftAlong f (f n) = f (n + 1) := by
  have h : ∃ m, f m = f n := ⟨n, rfl⟩
  have he : Nat.find h = n := f.injective (Nat.find_spec h)
  simp only [shiftAlong, dif_pos h, he]

private theorem shiftAlong_off (f : ℕ ↪ ι) (x : ι) (h : ¬ ∃ n, f n = x) :
    shiftAlong f x = x := by simp only [shiftAlong, dif_neg h]

private theorem shiftAlong_injective (f : ℕ ↪ ι) : Function.Injective (shiftAlong f) := by
  intro x y hxy
  by_cases hx : ∃ n, f n = x
  · obtain ⟨n, rfl⟩ := hx
    by_cases hy : ∃ m, f m = y
    · obtain ⟨m, rfl⟩ := hy
      rw [shiftAlong_on, shiftAlong_on] at hxy
      exact congrArg f (Nat.add_right_cancel (f.injective hxy))
    · rw [shiftAlong_on, shiftAlong_off f y hy] at hxy
      exact (hy ⟨n + 1, hxy⟩).elim
  · by_cases hy : ∃ m, f m = y
    · obtain ⟨m, rfl⟩ := hy
      rw [shiftAlong_off f x hx, shiftAlong_on] at hxy
      exact (hx ⟨m + 1, hxy.symm⟩).elim
    · simpa only [shiftAlong_off f x hx, shiftAlong_off f y hy] using hxy

private theorem shiftAlong_ne_zero (f : ℕ ↪ ι) (x : ι) :
    shiftAlong f x ≠ f 0 := by
  intro hx
  by_cases h : ∃ n, f n = x
  · obtain ⟨n, rfl⟩ := h
    rw [shiftAlong_on] at hx
    have : n + 1 = 0 := f.injective hx
    omega
  · rw [shiftAlong_off f x h] at hx
    exact h ⟨0, hx.symm⟩

/-- Missing ONE prescribed point, not merely an unspecified point. -/
theorem exists_embedding_avoiding_point [Infinite ι] (a : ι) :
    ∃ e : ι ↪ ι, ∀ x, e x ≠ a := by
  classical
  let f0 := Infinite.natEmbedding ι
  let f : ℕ ↪ ι := f0.trans (Equiv.swap (f0 0) a).toEmbedding
  have hf : f 0 = a := by simp [f]
  refine ⟨⟨shiftAlong f, shiftAlong_injective f⟩, ?_⟩
  intro x
  change shiftAlong f x ≠ a
  simpa only [hf] using shiftAlong_ne_zero f x

/-- Finite iteration deletes all specified coordinates from the range. -/
theorem exists_embedding_avoiding_finset [Infinite ι] (s : Finset ι) :
    ∃ e : ι ↪ ι, ∀ x, e x ∉ s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Function.Embedding.refl ι, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨e, he⟩ := ih
    by_cases hex : ∃ x, e x = a
    · obtain ⟨x, hx⟩ := hex
      obtain ⟨q, hq⟩ := exists_embedding_avoiding_point x
      refine ⟨q.trans e, ?_⟩
      intro y hmem
      rcases Finset.mem_insert.mp hmem with hya | hys
      · exact hq y (e.injective (hya.trans hx.symm))
      · exact he (q y) hys
    · refine ⟨e, ?_⟩
      intro y hmem
      rcases Finset.mem_insert.mp hmem with hya | hys
      · exact hex ⟨y, hya⟩
      · exact he y hys

end MathlibAnnex.FiniteCentral
