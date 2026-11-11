/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Order.Zorn
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.OrthogonalEquivalence
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.SchroederBernstein
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeDecomposition

/-!
# Proper infiniteness of type III projections

A nonfinite projection first supplies a nonzero properly infinite
subprojection. The construction sums the orthogonal defect sequence of an
internal proper isometry, and matches that sequence with its even and odd
subsequences.

For a type III projection, a maximal orthogonal family of such subprojections
exhausts the projection: any nonzero remainder is again nonfinite and would
supply a further member. The family may have arbitrary cardinality. Its two
families of internal witnesses are summed over all finite subsets using the
existing orthogonal-supremum equivalence theorem.

The existing nonzero predicate `IsProperlyInfiniteProjection` is used.
No countability, separability, factor, or sigma-finiteness assumption is made.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Orthogonality to a fixed projection passes to any projection supremum. -/
theorem iSupProjection_mul_eq_zero
    (M : VonNeumannAlgebra H) {ι : Type v}
    (P : ι → M.toStarSubalgebra) (hP : ∀ i, IsStarProjection (P i))
    {q : M.toStarSubalgebra} (hq : IsStarProjection q)
    (hzero : ∀ i, P i * q = 0) : iSupProjection M P hP * q = 0 := by
  have he : IsStarProjection (iSupProjection M P hP) :=
    isStarProjection_iSupProjection M P hP
  have hle : iSupProjection M P hP ≤ 1 - q := by
    apply iSupProjection_le M P hP hq.one_sub
    intro i
    apply ((hP i).le_iff_mul_eq_left hq.one_sub).2
    rw [mul_sub, mul_one, hzero i, sub_zero]
  have hmul : iSupProjection M P hP * (1 - q) = iSupProjection M P hP :=
    (he.le_iff_mul_eq_left hq.one_sub).1 hle
  calc
    iSupProjection M P hP * q =
        (iSupProjection M P hP * (1 - q)) * q := by rw [hmul]
    _ = 0 := by rw [mul_assoc, hq.one_sub_mul_self, mul_zero]

/-- If every member of one projection family is orthogonal to every member
of another, the two arbitrary projection suprema are orthogonal. -/
theorem iSupProjection_mul_iSupProjection_eq_zero
    (M : VonNeumannAlgebra H) {ι : Type v} {κ : Type w}
    (P : ι → M.toStarSubalgebra) (Q : κ → M.toStarSubalgebra)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hzero : ∀ i j, P i * Q j = 0) :
    iSupProjection M P hP * iSupProjection M Q hQ = 0 := by
  have he := isStarProjection_iSupProjection M P hP
  have hf := isStarProjection_iSupProjection M Q hQ
  have hright (j : κ) : iSupProjection M P hP * Q j = 0 :=
    iSupProjection_mul_eq_zero M P hP (hQ j) (fun i ↦ hzero i j)
  have hleft (j : κ) : Q j * iSupProjection M P hP = 0 := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq,
      (hQ j).isSelfAdjoint.star_eq, star_zero] using congrArg star (hright j)
  have hzero' : iSupProjection M Q hQ * iSupProjection M P hP = 0 :=
    iSupProjection_mul_eq_zero M Q hQ he hleft
  simpa only [star_mul, he.isSelfAdjoint.star_eq, hf.isSelfAdjoint.star_eq,
    star_zero] using congrArg star hzero'

private theorem mul_eq_zero_of_two_absorptions
    {M : VonNeumannAlgebra H} {a b r s : M.toStarSubalgebra}
    (ha : a * r = a) (hb : s * b = b) (hrs : r * s = 0) : a * b = 0 := by
  calc
    a * b = (a * r) * (s * b) := by rw [ha, hb]
    _ = a * (r * s) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hrs, mul_zero, zero_mul]

/-- The supremum of a nonzero orthogonal sequence of mutually equivalent
projections is properly infinite. The two copies are the even and odd
subsequence suprema, with witnesses in the same algebra. -/
theorem isProperlyInfiniteProjection_iSupProjection_nat
    (M : VonNeumannAlgebra H) (P : ℕ → M.toStarSubalgebra)
    (hP : ∀ n, IsStarProjection (P n))
    (horth : Pairwise (fun i j ↦ P i * P j = 0))
    (hstep : ∀ n, MurrayVonNeumannEquivalent (P n) (P (n + 1)))
    (hPzero : P 0 ≠ 0) : IsProperlyInfiniteProjection (iSupProjection M P hP) := by
  have hequiv : ∀ n, MurrayVonNeumannEquivalent (P 0) (P n) := by
    intro n
    induction n with
    | zero => exact MurrayVonNeumannEquivalent.refl (hP 0)
    | succ n ih => exact ih.trans (hstep n)
  let Q : ℕ → M.toStarSubalgebra := fun n ↦ P (2 * n)
  let R : ℕ → M.toStarSubalgebra := fun n ↦ P (2 * n + 1)
  have hQ (n : ℕ) : IsStarProjection (Q n) := hP (2 * n)
  have hR (n : ℕ) : IsStarProjection (R n) := hP (2 * n + 1)
  have hQorth : Pairwise (fun i j ↦ Q i * Q j = 0) := by
    intro i j hij
    exact horth (by omega : 2 * i ≠ 2 * j)
  have hRorth : Pairwise (fun i j ↦ R i * R j = 0) := by
    intro i j hij
    exact horth (by omega : 2 * i + 1 ≠ 2 * j + 1)
  have hcross (i j : ℕ) : Q i * R j = 0 :=
    horth (by omega : 2 * i ≠ 2 * j + 1)
  let e := iSupProjection M P hP
  let q := iSupProjection M Q hQ
  let r := iSupProjection M R hR
  have he : IsStarProjection e := isStarProjection_iSupProjection M P hP
  have hq : IsStarProjection q := isStarProjection_iSupProjection M Q hQ
  have hr : IsStarProjection r := isStarProjection_iSupProjection M R hR
  have heq : MurrayVonNeumannEquivalent e q :=
    murrayVonNeumannEquivalent_iSupProjection M P Q hP hQ horth hQorth
      (fun n ↦ (hequiv n).symm.trans (hequiv (2 * n)))
  have her : MurrayVonNeumannEquivalent e r :=
    murrayVonNeumannEquivalent_iSupProjection M P R hP hR horth hRorth
      (fun n ↦ (hequiv n).symm.trans (hequiv (2 * n + 1)))
  have hqe : q ≤ e := iSupProjection_le M Q hQ he
    (fun n ↦ le_iSupProjection M P hP (2 * n))
  have hre : r ≤ e := iSupProjection_le M R hR he
    (fun n ↦ le_iSupProjection M P hP (2 * n + 1))
  have he0 : e ≠ 0 := by
    intro h
    have hfix : P 0 * e = P 0 :=
      ((hP 0).le_iff_mul_eq_left he).1 (le_iSupProjection M P hP 0)
    rw [h, mul_zero] at hfix
    exact hPzero hfix.symm
  exact ⟨he, he0, q, r, heq, her,
    (hq.le_iff_mul_eq_left he).1 hqe, (hr.le_iff_mul_eq_left he).1 hre,
    iSupProjection_mul_iSupProjection_eq_zero M Q R hQ hR hcross⟩

/-- Every nonfinite internal projection contains a nonzero properly infinite
subprojection. The containing projection itself need not be properly infinite. -/
theorem exists_isProperlyInfiniteProjection_le_of_not_isFiniteProjection
    (M : VonNeumannAlgebra H) {p : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hfinite : ¬ IsFiniteProjection p) :
    ∃ e : M.toStarSubalgebra, IsProperlyInfiniteProjection e ∧ e ≤ p := by
  classical
  have hexists : ∃ q : M.toStarSubalgebra,
      MurrayVonNeumannEquivalent p q ∧ q * p = q ∧ q ≠ p := by
    by_contra hnone
    apply hfinite
    refine ⟨hp, ?_⟩
    intro q hpq hqp
    by_contra hne
    exact hnone ⟨q, hpq, hqp, hne⟩
  obtain ⟨q, hpq, hqp, hne⟩ := hexists
  obtain ⟨P, hP, hPzero, hPp, horth, hstep⟩ := hpq.exists_orthogonal_sequence hqp
  have hdefect : P 0 ≠ 0 := by
    rw [hPzero]
    intro h
    exact hne (sub_eq_zero.mp h).symm
  refine ⟨iSupProjection M P hP,
    isProperlyInfiniteProjection_iSupProjection_nat M P hP horth hstep hdefect, ?_⟩
  exact iSupProjection_le M P hP hp
    (fun n ↦ ((hP n).le_iff_mul_eq_left hp).2 (hPp n))


/-- A nonzero supremum of an arbitrary orthogonal family of properly infinite
projections is properly infinite. Empty families are excluded only by the
explicit nonzero hypothesis on the supremum. -/
theorem isProperlyInfiniteProjection_iSupProjection
    (M : VonNeumannAlgebra H) {ι : Type v}
    (P : ι → M.toStarSubalgebra)
    (hP : ∀ i, IsProperlyInfiniteProjection (P i))
    (horth : Pairwise (fun i j ↦ P i * P j = 0))
    (hne : iSupProjection M P (fun i ↦ (hP i).1) ≠ 0) :
    IsProperlyInfiniteProjection (iSupProjection M P (fun i ↦ (hP i).1)) := by
  classical
  let R : ι → M.toStarSubalgebra := fun i ↦ (hP i).2.2.choose
  let S : ι → M.toStarSubalgebra := fun i ↦ (hP i).2.2.choose_spec.choose
  have hdata (i : ι) :
      MurrayVonNeumannEquivalent (P i) (R i) ∧
      MurrayVonNeumannEquivalent (P i) (S i) ∧
      R i * P i = R i ∧ S i * P i = S i ∧ R i * S i = 0 :=
    (hP i).2.2.choose_spec.choose_spec
  have hp (i : ι) : IsStarProjection (P i) := (hP i).1
  have hR (i : ι) : IsStarProjection (R i) := (hdata i).1.isStarProjection_right
  have hS (i : ι) : IsStarProjection (S i) := (hdata i).2.1.isStarProjection_right
  have hRP (i : ι) : R i * P i = R i := (hdata i).2.2.1
  have hSP (i : ι) : S i * P i = S i := (hdata i).2.2.2.1
  have hRS (i : ι) : R i * S i = 0 := (hdata i).2.2.2.2
  have hPR (i : ι) : P i * R i = R i := by
    simpa only [star_mul, (hp i).isSelfAdjoint.star_eq,
      (hR i).isSelfAdjoint.star_eq] using congrArg star (hRP i)
  have hPS (i : ι) : P i * S i = S i := by
    simpa only [star_mul, (hp i).isSelfAdjoint.star_eq,
      (hS i).isSelfAdjoint.star_eq] using congrArg star (hSP i)
  have hRorth : Pairwise (fun i j ↦ R i * R j = 0) := by
    intro i j hij
    exact mul_eq_zero_of_two_absorptions (hRP i) (hPR j) (horth hij)
  have hSorth : Pairwise (fun i j ↦ S i * S j = 0) := by
    intro i j hij
    exact mul_eq_zero_of_two_absorptions (hSP i) (hPS j) (horth hij)
  have hcross (i j : ι) : R i * S j = 0 := by
    by_cases hij : i = j
    · subst j
      exact hRS i
    · exact mul_eq_zero_of_two_absorptions (hRP i) (hPS j) (horth hij)
  let e := iSupProjection M P hp
  let r := iSupProjection M R hR
  let s := iSupProjection M S hS
  have he : IsStarProjection e := isStarProjection_iSupProjection M P hp
  have hr : IsStarProjection r := isStarProjection_iSupProjection M R hR
  have hs : IsStarProjection s := isStarProjection_iSupProjection M S hS
  have her : MurrayVonNeumannEquivalent e r :=
    murrayVonNeumannEquivalent_iSupProjection M P R hp hR horth hRorth
      (fun i ↦ (hdata i).1)
  have hes : MurrayVonNeumannEquivalent e s :=
    murrayVonNeumannEquivalent_iSupProjection M P S hp hS horth hSorth
      (fun i ↦ (hdata i).2.1)
  have hre : r ≤ e := by
    apply iSupProjection_le M R hR he
    intro i
    exact (((hR i).le_iff_mul_eq_left (hp i)).2 (hRP i)).trans
      (le_iSupProjection M P hp i)
  have hse : s ≤ e := by
    apply iSupProjection_le M S hS he
    intro i
    exact (((hS i).le_iff_mul_eq_left (hp i)).2 (hSP i)).trans
      (le_iSupProjection M P hp i)
  exact ⟨he, hne, r, s, her, hes,
    (hr.le_iff_mul_eq_left he).1 hre, (hs.le_iff_mul_eq_left he).1 hse,
    iSupProjection_mul_iSupProjection_eq_zero M R S hR hS hcross⟩

private theorem exists_maximal_orthogonal_family
    (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) :
    ∃ s : Set M.toStarSubalgebra,
      (∀ q ∈ s, IsProperlyInfiniteProjection q ∧ q * p = q) ∧
      s.Pairwise (fun q r ↦ q * r = 0) ∧
      ∀ t : Set M.toStarSubalgebra,
        (∀ q ∈ t, IsProperlyInfiniteProjection q ∧ q * p = q) →
        t.Pairwise (fun q r ↦ q * r = 0) →
        s ⊆ t → t ⊆ s := by
  classical
  let F : Set (Set M.toStarSubalgebra) := {s |
    (∀ q ∈ s, IsProperlyInfiniteProjection q ∧ q * p = q) ∧
      s.Pairwise (fun q r ↦ q * r = 0)}
  have hchain : ∀ c ⊆ F, IsChain (· ⊆ ·) c →
      ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hordered
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    · intro q hq
      obtain ⟨s, hs, hqs⟩ := Set.mem_sUnion.mp hq
      exact (hc hs).1 q hqs
    · intro q hq r hr hqr
      obtain ⟨s, hs, hqs⟩ := Set.mem_sUnion.mp hq
      obtain ⟨t, ht, hrt⟩ := Set.mem_sUnion.mp hr
      rcases hordered.total hs ht with hst | hts
      · exact (hc ht).2 (hst hqs) hrt hqr
      · exact (hc hs).2 hqs (hts hrt) hqr
  obtain ⟨s, hs⟩ := zorn_subset F hchain
  exact ⟨s, hs.1.1, hs.1.2,
    fun t ht horth hst ↦ hs.2 ⟨ht, horth⟩ hst⟩

/-- Every nonzero type III projection is properly infinite in its specified
von Neumann algebra. The type III condition is applied to every nonzero
remainder of a maximal arbitrary orthogonal family. -/
theorem IsTypeIIIProjection.isProperlyInfiniteProjection
    {M : VonNeumannAlgebra H} {p : M.toStarSubalgebra}
    (hp : IsTypeIIIProjection M p) (hp0 : p ≠ 0) :
    IsProperlyInfiniteProjection p := by
  classical
  obtain ⟨s, hs, horth, hmax⟩ := exists_maximal_orthogonal_family M p
  let P : s → M.toStarSubalgebra := fun i ↦ i.1
  have hP (i : s) : IsProperlyInfiniteProjection (P i) := (hs i.1 i.2).1
  have hproj (i : s) : IsStarProjection (P i) := (hP i).1
  have hPorth : Pairwise (fun i j ↦ P i * P j = 0) := by
    intro i j hij
    exact horth i.2 j.2 (fun h ↦ hij (Subtype.ext h))
  let e := iSupProjection M P hproj
  have he : IsStarProjection e := isStarProjection_iSupProjection M P hproj
  have hep_le : e ≤ p := iSupProjection_le M P hproj hp.1
    (fun i ↦ ((hproj i).le_iff_mul_eq_left hp.1).2 (hs i.1 i.2).2)
  have hep : e * p = e := (he.le_iff_mul_eq_left hp.1).1 hep_le
  let d : M.toStarSubalgebra := p - e
  have hd : IsStarProjection d := he.sub_of_mul_eq_left hp.1 hep
  have hdp : d * p = d := by
    change (p - e) * p = p - e
    rw [sub_mul, hp.1.isIdempotentElem.eq, hep]
  have hed : e * d = 0 := by
    change e * (p - e) = 0
    rw [mul_sub, hep, he.isIdempotentElem.eq, sub_self]
  have hd0 : d = 0 := by
    by_contra hd0
    have hnonfinite : ¬ IsFiniteProjection d := fun hfin ↦ hd0 (hp.2 d hfin hdp)
    obtain ⟨f, hf, hfd_le⟩ :=
      exists_isProperlyInfiniteProjection_le_of_not_isFiniteProjection M hd hnonfinite
    have hfd : f * d = f := (hf.1.le_iff_mul_eq_left hd).1 hfd_le
    have hdf : d * f = f := (hf.1.le_iff_mul_eq_right hd).1 hfd_le
    have hfp : f * p = f := by
      calc
        f * p = (f * d) * p := by rw [hfd]
        _ = f * (d * p) := mul_assoc _ _ _
        _ = f := by rw [hdp, hfd]
    have hcross (r : M.toStarSubalgebra) (hr : r ∈ s) : r * f = 0 := by
      have hre : r * e = r :=
        ((hs r hr).1.1.le_iff_mul_eq_left he).1
          (le_iSupProjection M P hproj ⟨r, hr⟩)
      exact mul_eq_zero_of_two_absorptions hre hdf hed
    have hcross' (r : M.toStarSubalgebra) (hr : r ∈ s) : f * r = 0 := by
      simpa only [star_mul, hf.1.isSelfAdjoint.star_eq,
        (hs r hr).1.1.isSelfAdjoint.star_eq, star_zero]
        using congrArg star (hcross r hr)
    have hnew : ∀ q ∈ insert f s, IsProperlyInfiniteProjection q ∧ q * p = q := by
      intro q hq
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · exact ⟨hf, hfp⟩
      · exact hs q hq
    have hneworth : (insert f s).Pairwise (fun q r ↦ q * r = 0) := by
      intro q hq r hr hqr
      rcases Set.mem_insert_iff.mp hq with hqf | hqs
      · rcases Set.mem_insert_iff.mp hr with hrf | hrs
        · exact (hqr (hqf.trans hrf.symm)).elim
        · rw [hqf]
          exact hcross' r hrs
      · rcases Set.mem_insert_iff.mp hr with hrf | hrs
        · rw [hrf]
          exact hcross q hqs
        · exact horth hqs hrs hqr
    have hfs : f ∈ s :=
      hmax (insert f s) hnew hneworth (Set.subset_insert f s) (Set.mem_insert f s)
    have hff : f * f = 0 := hcross f hfs
    exact hf.ne_zero (hf.1.isIdempotentElem.eq.symm.trans hff)
  have hep_eq : e = p := (sub_eq_zero.mp hd0).symm
  have hproper : IsProperlyInfiniteProjection e :=
    isProperlyInfiniteProjection_iSupProjection M P hP hPorth (by
      change e ≠ 0
      rwa [hep_eq])
  simpa only [hep_eq] using hproper

/-- Every nonzero projection in a type III algebra is properly infinite.
The zero algebra requires no additional special hypothesis. -/
theorem IsTypeIII.isProperlyInfiniteProjection
    {M : VonNeumannAlgebra H} (hM : IsTypeIII M)
    {p : M.toStarSubalgebra} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    IsProperlyInfiniteProjection p := by
  have hpIII : IsTypeIIIProjection M p :=
    ⟨hp, fun q hq _ ↦ hM.2 q hq (mul_one q)⟩
  exact hpIII.isProperlyInfiniteProjection hp0

end VonNeumannAlgebra
