import Mathlib

/-!
# Compact convex hulls in finite real coordinate spaces

This file proves compactness of the convex hull of a compact subset of a finite
real Pi space.  Mathlib supplies the finite-set theorem and the finite
Carathéodory representation; the remaining compact-parameter argument is kept
here as the actual Annex delta.
-/

noncomputable section

open Set Finset
open scoped BigOperators

namespace MathlibAnnex

/-- Coefficients and points for a convex combination with exactly `k` slots. -/
private def fixedConvexCarrier {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (k : ℕ) :
    Set ((Fin k → ℝ) × (Fin k → ι → ℝ)) :=
  (stdSimplex ℝ (Fin k)) ×ˢ (Set.univ.pi fun _ : Fin k => s)

/-- Evaluation of a fixed-length convex combination. -/
private def fixedConvexEval {ι : Type*} [Fintype ι] {k : ℕ}
    (q : (Fin k → ℝ) × (Fin k → ι → ℝ)) : ι → ℝ :=
  ∑ i, q.1 i • q.2 i

/-- The set of all convex combinations with exactly `k` slots. -/
private def fixedConvexImage {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (k : ℕ) : Set (ι → ℝ) :=
  fixedConvexEval '' fixedConvexCarrier s k

private theorem isCompact_fixedConvexCarrier {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsCompact s) (k : ℕ) :
    IsCompact (fixedConvexCarrier s k) := by
  have hw : IsCompact (stdSimplex ℝ (Fin k)) :=
    isCompact_stdSimplex ℝ (Fin k)
  have hz : IsCompact (Set.univ.pi fun _ : Fin k => s) := by
    exact isCompact_univ_pi (fun _ => hs)
  exact hw.prod hz

private theorem continuous_fixedConvexEval {ι : Type*} [Fintype ι] {k : ℕ} :
    Continuous (fixedConvexEval :
      ((Fin k → ℝ) × (Fin k → ι → ℝ)) → (ι → ℝ)) := by
  unfold fixedConvexEval
  fun_prop

private theorem isCompact_fixedConvexImage {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsCompact s) (k : ℕ) :
    IsCompact (fixedConvexImage s k) := by
  exact (isCompact_fixedConvexCarrier hs k).image continuous_fixedConvexEval

private theorem affineIndependent_card_le_pi_succ {ι κ : Type*}
    [Fintype ι] [Fintype κ] {z : κ → ι → ℝ}
    (hz : AffineIndependent ℝ z) :
    Fintype.card κ ≤ Fintype.card ι + 1 := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl hκ => simp
  | inr hκ =>
      let i0 : κ := Classical.choice hκ
      have hlin :=
        (affineIndependent_iff_linearIndependent_vsub ℝ z i0).1 hz
      have hcard : Fintype.card {i : κ // i ≠ i0} ≤ Fintype.card ι := by
        exact (Pi.basisFun ℝ ι).card_le_card_of_linearIndependent hlin
      have hsubcard :
          Fintype.card {i : κ // i ≠ i0} = Fintype.card κ - 1 := by
        calc
          Fintype.card {i : κ // i ≠ i0} =
              Fintype.card κ - Fintype.card {i : κ // i = i0} :=
            Fintype.card_subtype_compl (fun i : κ => i = i0)
          _ = Fintype.card κ - 1 := by
            rw [Fintype.card_subtype_eq i0]
      have hκcard_pos : 0 < Fintype.card κ :=
        Fintype.card_pos_iff.mpr hκ
      omega

private theorem exists_bounded_convex_representation {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} {x : ι → ℝ} (hx : x ∈ convexHull ℝ s) :
    ∃ k : Fin (Fintype.card ι + 2), x ∈ fixedConvexImage s k.1 := by
  classical
  rcases eq_pos_convex_span_of_mem_convexHull hx with
    ⟨κ, hκ, z, w, hz, hind, hwpos, hwsum, hvalue⟩
  letI : Fintype κ := hκ
  have hk : Fintype.card κ < Fintype.card ι + 2 := by
    have := affineIndependent_card_le_pi_succ hind
    omega
  let k : Fin (Fintype.card ι + 2) := ⟨Fintype.card κ, hk⟩
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let w' : Fin k.1 → ℝ := fun j => w (e.symm j)
  let z' : Fin k.1 → ι → ℝ := fun j => z (e.symm j)
  refine ⟨k, ⟨(w', z'), ?_, ?_⟩⟩
  · constructor
    · change (∀ j : Fin k.1, 0 ≤ w' j) ∧ ∑ j, w' j = 1
      refine ⟨fun j => (hwpos (e.symm j)).le, ?_⟩
      have hsum :
          (∑ j : Fin (Fintype.card κ), w (e.symm j)) = ∑ i : κ, w i :=
        Equiv.sum_comp e.symm w
      simpa [k, w'] using hsum.trans hwsum
    · intro j hj
      exact hz ⟨e.symm j, rfl⟩
  · change ∑ j : Fin k.1, w' j • z' j = x
    calc
      (∑ j : Fin k.1, w' j • z' j) = ∑ i : κ, w i • z i := by
        have hsum :
            (∑ j : Fin (Fintype.card κ), w (e.symm j) • z (e.symm j)) =
              ∑ i : κ, w i • z i :=
          Equiv.sum_comp e.symm (fun i : κ => w i • z i)
        simpa [k, w', z'] using hsum
      _ = x := hvalue

private theorem fixedConvexImage_subset_convexHull {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (k : ℕ) :
    fixedConvexImage s k ⊆ convexHull ℝ s := by
  rintro x ⟨q, hq, rfl⟩
  rcases hq with ⟨hw, hz⟩
  have hc := convex_convexHull ℝ s
  change (∀ i, 0 ≤ q.1 i) ∧ ∑ i, q.1 i = 1 at hw
  have hmem := hc.sum_mem (t := Finset.univ) (w := q.1) (z := q.2)
    (fun i _ => hw.1 i)
    (by simpa using hw.2)
    (fun i _ => subset_convexHull ℝ s (hz i (mem_univ i)))
  simpa [fixedConvexEval] using hmem

private theorem convexHull_eq_iUnion_fixedConvexImage {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) :
    convexHull ℝ s =
      ⋃ k : Fin (Fintype.card ι + 2), fixedConvexImage s k.1 := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases exists_bounded_convex_representation hx with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k, hk⟩
  · exact iUnion_subset fun k => fixedConvexImage_subset_convexHull s k.1

/-- The convex hull of a compact subset of a finite real Pi space is compact. -/
theorem isCompact_convexHull_pi {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [convexHull_eq_iUnion_fixedConvexImage]
  exact isCompact_iUnion fun k => isCompact_fixedConvexImage hs k.1

end MathlibAnnex
