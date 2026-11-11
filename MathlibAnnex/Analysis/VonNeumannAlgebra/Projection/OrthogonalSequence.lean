/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.

The strong convergence proof reuses the arbitrary-family summability theorem
in Projection/OrthogonalSum.lean.  Its finite-sum bound uses Mathlib's existing
IsStarProjection.add and norm_le.  No operator-norm convergence of an infinite
projection sum, finite-rank interpretation, or separability is assumed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalSum
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.FiniteDimensional
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.FiniteFactor

/-!
# Strongly null projection sequences in diffuse corners

Absence of internal minimal projections permits repeated proper splitting
inside any nonzero projection.  Successive differences are nonzero and
orthogonal.  Pointwise summability makes the sequence strongly null, whereas
each nonzero projection still has norm one.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped BigOperators CStarAlgebra InnerProduct

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Pairwise orthogonal projections tend strongly to zero.  The assertion
holds on an arbitrary Hilbert space and does not concern operator norm. -/
theorem stronglyConverges_zero_of_pairwise_orthogonal_projections
    (p : ℕ → H →L[ℂ] H) (hp : ∀ n, IsStarProjection (p n))
    (horth : Pairwise (fun i j ↦ p i * p j = 0)) :
    StronglyConverges p atTop 0 := by
  classical
  have hsum : ∀ s : Finset ℕ, IsStarProjection (∑ i ∈ s, p i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using IsStarProjection.zero (H →L[ℂ] H)
    | @insert n s hns ih =>
        rw [Finset.sum_insert hns]
        apply (hp n).add ih
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro m hm
        apply horth
        intro hnm
        subst m
        exact hns hm
  have hbound (s : Finset ℕ) (x : H) : ‖(∑ i ∈ s, p i) x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using
      (∑ i ∈ s, p i).le_of_opNorm_le (IsStarProjection.norm_le _ (hsum s)) x
  have horth' : Pairwise (fun i j ↦ (p i)†.comp (p j) = 0) := by
    intro i j hij
    change star (p i) * p j = 0
    simpa only [(hp i).isSelfAdjoint.star_eq] using horth hij
  intro x
  simpa only [zero_apply] using
    (summable_apply_of_orthogonal_of_finset_bound p horth' hbound x).tendsto_atTop_zero

end ContinuousLinearMap

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The accepted II₁ predicate has no internal minimal projection, with
no assumption on the multiplicity of its concrete representation. The
minimal-to-abelian implication is the existing `TypeI.FiniteDimensional`
provider; it is not redeclared here. -/
theorem IsTypeII1.not_isMinimalStarProjection
    {M : VonNeumannAlgebra H} (hM : M.IsTypeII1) (p : M.toStarSubalgebra) :
    ¬ IsMinimalStarProjection p := by
  intro hp
  exact hp.ne_zero
    (hM.eq_zero_of_abelian_projection (M.isAbelianProjection_of_isMinimalStarProjection hp))

/-- Repeated proper splitting gives an actual countable orthogonal family
of nonzero subprojections in every nonzero diffuse corner. -/
theorem exists_orthogonal_sequence_of_no_minimal_projection
    (M : VonNeumannAlgebra H)
    (hM : ∀ r : M.toStarSubalgebra, ¬ IsMinimalStarProjection r)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → M.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≠ 0 ∧ q n ≤ p) ∧
      Pairwise (fun i j ↦ q i * q j = 0) := by
  classical
  have hsplit : ∀ r : M.toStarSubalgebra, IsStarProjection r → r ≠ 0 →
      ∃ s : M.toStarSubalgebra, IsStarProjection s ∧ s ≠ 0 ∧ s ≤ r ∧ s ≠ r := by
    intro r hr hr0
    by_contra h
    apply hM r
    refine ⟨hr, hr0, ?_⟩
    intro s hs hs0 hsr
    by_contra hne
    exact h ⟨s, hs, hs0, hsr, hne⟩
  let P := {r : M.toStarSubalgebra // IsStarProjection r ∧ r ≠ 0}
  have hstep : ∀ r : P, ∃ s : P, s.1 < r.1 := by
    intro r
    obtain ⟨s, hs, hs0, hsr, hne⟩ := hsplit r.1 r.2.1 r.2.2
    exact ⟨⟨s, hs, hs0⟩, lt_of_le_of_ne hsr hne⟩
  choose next hnext using hstep
  let r : ℕ → P := fun n ↦ Nat.rec ⟨p, hp, hp0⟩ (fun _ x ↦ next x) n
  have hsucc (n : ℕ) : (r (n + 1)).1 < (r n).1 := hnext (r n)
  have hanti : Antitone (fun n ↦ (r n).1) :=
    antitone_nat_of_succ_le (fun n ↦ (hsucc n).le)
  have hrp (n : ℕ) : (r n).1 ≤ p := hanti (Nat.zero_le n)
  let q : ℕ → M.toStarSubalgebra := fun n ↦ (r n).1 - (r (n + 1)).1
  have hq (n : ℕ) : IsStarProjection (q n) :=
    ((r (n + 1)).2.1.le_iff_sub (r n).2.1).mp (hsucc n).le
  have hq0 (n : ℕ) : q n ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (hsucc n))
  have hqr (n : ℕ) : q n ≤ (r n).1 :=
    sub_le_self _ (r (n + 1)).2.1.nonneg
  have hordered (i j : ℕ) (hij : i < j) : q i * q j = 0 := by
    have hji : q j ≤ (r i).1 := (hqr j).trans (hanti hij.le)
    have hjs : q j ≤ (r (i + 1)).1 :=
      (hqr j).trans (hanti (Nat.succ_le_of_lt hij))
    change ((r i).1 - (r (i + 1)).1) * q j = 0
    rw [sub_mul, ((hq j).le_iff_mul_eq_right (r i).2.1).mp hji,
      ((hq j).le_iff_mul_eq_right (r (i + 1)).2.1).mp hjs, sub_self]
  refine ⟨q, fun n ↦ ⟨hq n, hq0 n, (hqr n).trans (hrp n)⟩, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h
  · simpa only [star_mul, (hq i).isSelfAdjoint.star_eq,
      (hq j).isSelfAdjoint.star_eq, star_zero] using congrArg star (hordered j i h)

/-- A diffuse nonzero corner contains a strongly null projection sequence
whose operator norms are all one.  This is the concrete obstruction to
norm continuity on its strong unit ball. -/
theorem exists_stronglyConverges_zero_projection_sequence_of_no_minimal_projection
    (M : VonNeumannAlgebra H)
    (hM : ∀ r : M.toStarSubalgebra, ¬ IsMinimalStarProjection r)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → M.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≤ p ∧ ‖q n‖ = 1) ∧
      Pairwise (fun i j ↦ q i * q j = 0) ∧
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (q n : H →L[ℂ] H)) atTop 0 := by
  obtain ⟨q, hq, horth⟩ := M.exists_orthogonal_sequence_of_no_minimal_projection hM hp hp0
  have hnorm (n : ℕ) : ‖q n‖ = 1 := by
    have hsq := CStarRing.norm_star_mul_self (x := q n)
    rw [(hq n).1.isSelfAdjoint.star_eq, (hq n).1.isIdempotentElem.eq] at hsq
    have hpos : 0 < ‖q n‖ := norm_pos_iff.mpr (hq n).2.1
    nlinarith
  refine ⟨q, fun n ↦ ⟨(hq n).1, (hq n).2.2, hnorm n⟩, horth, ?_⟩
  apply ContinuousLinearMap.stronglyConverges_zero_of_pairwise_orthogonal_projections
    (fun n ↦ (q n : H →L[ℂ] H))
    (fun n ↦ (hq n).1.map M.toStarSubalgebra.subtype)
  intro i j hij
  exact congrArg (fun a : M.toStarSubalgebra ↦ (a : H →L[ℂ] H)) (horth hij)

/-- In particular every nonzero corner of the same accepted II₁ algebra
has a strongly null, norm-one sequence of projections. -/
theorem IsTypeII1.exists_stronglyConverges_zero_projection_sequence
    {M : VonNeumannAlgebra H} (hM : M.IsTypeII1)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : ℕ → M.toStarSubalgebra,
      (∀ n, IsStarProjection (q n) ∧ q n ≤ p ∧ ‖q n‖ = 1) ∧
      Pairwise (fun i j ↦ q i * q j = 0) ∧
      ContinuousLinearMap.StronglyConverges
        (fun n ↦ (q n : H →L[ℂ] H)) atTop 0 :=
  M.exists_stronglyConverges_zero_projection_sequence_of_no_minimal_projection
    hM.not_isMinimalStarProjection hp hp0

end VonNeumannAlgebra
