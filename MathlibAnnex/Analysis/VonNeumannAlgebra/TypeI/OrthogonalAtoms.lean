/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in THIRD_PARTY_NOTICES.md.
-/

import Mathlib.Order.Zorn
import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Factor

/-!
# Orthogonal copies of a minimal projection

Zorn's lemma gives a maximal set of internal partial isometries with a
fixed initial projection and pairwise orthogonal final projections.
In a factor, a fixed nonzero minimal projection can be moved into every
nonzero residual projection. Maximality therefore makes the supremum of
the final projections equal to one.

The family is indexed by a subset of the given algebra. There is no
countability, separability, or enumeration assumption.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra

namespace VonNeumannAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An arbitrary projection admits a maximal family of internal partial
isometries with that common initial projection and orthogonal finals.
The projection itself belongs to the family. -/
theorem exists_maximal_orthogonal_partial_isometries
    (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) (hp : IsStarProjection p) :
    ∃ s : Set M.toStarSubalgebra,
      p ∈ s ∧
      (∀ v ∈ s, IsPartialIsometry v ∧ star v * v = p) ∧
      s.Pairwise (fun v w ↦ (v * star v) * (w * star w) = 0) ∧
      ∀ t : Set M.toStarSubalgebra,
        (∀ v ∈ t, IsPartialIsometry v ∧ star v * v = p) →
        t.Pairwise (fun v w ↦ (v * star v) * (w * star w) = 0) →
        s ⊆ t → t ⊆ s := by
  classical
  let F : Set (Set M.toStarSubalgebra) := {s |
    (∀ v ∈ s, IsPartialIsometry v ∧ star v * v = p) ∧
    s.Pairwise (fun v w ↦ (v * star v) * (w * star w) = 0)}
  have hseed : ({p} : Set M.toStarSubalgebra) ∈ F := by
    constructor
    · intro v hv
      have hvp : v = p := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨hp.isPartialIsometry, by rw [hp.isSelfAdjoint.star_eq,
        hp.isIdempotentElem.eq]⟩
    · intro v hv w hw hvw
      exact (hvw ((Set.mem_singleton_iff.mp hv).trans
        (Set.mem_singleton_iff.mp hw).symm)).elim
  have hchain : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ F, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hordered _
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      exact (hc hs).1 v hvs
    · intro v hv w hw hvw
      obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
      obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
      rcases hordered.total hs ht with hst | hts
      · exact (hc ht).2 (hst hvs) hwt hvw
      · exact (hc hs).2 hvs (hts hwt) hvw
  obtain ⟨s, hps, hs⟩ := zorn_subset_nonempty F hchain {p} hseed
  exact ⟨s, hps (Set.mem_singleton p), hs.1.1, hs.1.2,
    fun t hinitial horth hst ↦ hs.2 ⟨hinitial, horth⟩ hst⟩

/-- In a factor, orthogonal internal copies of a fixed minimal projection
can be chosen so that their final projections exhaust the unit. The
witness type and its common initial projection stay inside the original
algebra. -/
theorem IsFactor.exists_orthogonal_partial_isometries_of_minimal_projection
    {M : VonNeumannAlgebra H} (hM : IsFactor M) {p : M.toStarSubalgebra}
    (hp : MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p) :
    ∃ s : Set M.toStarSubalgebra, p ∈ s ∧
      ∃ hs : ∀ v ∈ s, IsPartialIsometry v ∧ star v * v = p,
        s.Pairwise (fun v w ↦ (v * star v) * (w * star w) = 0) ∧
        iSupProjection M (fun v : s ↦ (v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra))
          (fun v ↦ (hs v.1 v.2).1.isStarProjection_mul_star_self) = 1 := by
  classical
  obtain ⟨s, hps, hs, horth, hmax⟩ :=
    exists_maximal_orthogonal_partial_isometries M p hp.1
  refine ⟨s, hps, hs, horth, ?_⟩
  let f : s → M.toStarSubalgebra := fun v ↦
    (v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra)
  have hf : ∀ v, IsStarProjection (f v) :=
    fun v ↦ (hs v.1 v.2).1.isStarProjection_mul_star_self
  let z : M.toStarSubalgebra := iSupProjection M f hf
  have hz : IsStarProjection z := isStarProjection_iSupProjection M f hf
  change z = 1
  by_contra hne
  have hc0 : (1 - z : M.toStarSubalgebra) ≠ 0 := by
    intro h
    exact hne (sub_eq_zero.mp h).symm
  obtain ⟨q, hpq, hq0, hqc⟩ :=
    hM.exists_equivalent_subprojection_of_minimal_projection hp hz.one_sub hc0
  obtain ⟨v, hv, hi, hfinal⟩ := hpq.2.2
  have hcz : (1 - z) * q = q := (hpq.2.1.le_iff_mul_eq_right hz.one_sub).1 hqc
  have hzq : z * q = 0 := by
    calc
      z * q = z * ((1 - z) * q) := by rw [hcz]
      _ = (z * (1 - z)) * q := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hz.mul_one_sub_self, zero_mul]
  have hcross (w : M.toStarSubalgebra) (hw : w ∈ s) :
      (w * star w) * (v * star v) = 0 := by
    have hwproj := (hs w hw).1.isStarProjection_mul_star_self
    have hwle : w * star w ≤ z := le_iSupProjection M f hf ⟨w, hw⟩
    have hwz : (w * star w) * z = w * star w :=
      (hwproj.le_iff_mul_eq_left hz).1 hwle
    rw [hfinal]
    calc
      (w * star w) * q = ((w * star w) * z) * q := by rw [hwz]
      _ = (w * star w) * (z * q) := mul_assoc _ _ _
      _ = 0 := by rw [hzq, mul_zero]
  have hcross' (w : M.toStarSubalgebra) (hw : w ∈ s) :
      (v * star v) * (w * star w) = 0 := by
    simpa only [star_mul, star_star,
      (hs w hw).1.isStarProjection_mul_star_self.isSelfAdjoint.star_eq,
      hv.isStarProjection_mul_star_self.isSelfAdjoint.star_eq, star_zero]
      using congrArg star (hcross w hw)
  have hvinitial : ∀ w ∈ insert v s, IsPartialIsometry w ∧ star w * w = p := by
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact ⟨hv, hi⟩
    · exact hs w hw
  have hvorth : (insert v s).Pairwise
      (fun a b ↦ (a * star a) * (b * star b) = 0) := by
    intro a ha b hb hab
    rcases Set.mem_insert_iff.mp ha with hav | has
    · rcases Set.mem_insert_iff.mp hb with hbv | hbs
      · exact (hab (hav.trans hbv.symm)).elim
      · exact hav ▸ hcross' b hbs
    · rcases Set.mem_insert_iff.mp hb with hbv | hbs
      · rw [hbv]
        exact hcross a has
      · exact horth has hbs hab
  have hvins : v ∈ s :=
    hmax (insert v s) hvinitial hvorth (Set.subset_insert v s) (Set.mem_insert v s)
  have hzero : q = 0 := by
    have h := hcross v hvins
    rw [hfinal, hpq.2.1.isIdempotentElem.eq] at h
    exact h
  exact hq0 hzero

/-- A type I factor has a nonempty, possibly uncountable family of
orthogonal abelian atoms with common internal partial-isometry source. -/
theorem IsFactor.exists_orthogonal_abelian_atoms
    {M : VonNeumannAlgebra H} (hM : IsFactor M) (hI : IsTypeI M) :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧
      MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection p ∧
      ∃ s : Set M.toStarSubalgebra, p ∈ s ∧
        ∃ hs : ∀ v ∈ s, IsPartialIsometry v ∧ star v * v = p,
          s.Pairwise (fun v w ↦ (v * star v) * (w * star w) = 0) ∧
          (∀ v ∈ s, IsAbelianProjection M (v * star v) ∧
            MathlibAnnex.Analysis.CStarAlgebra.IsMinimalStarProjection (v * star v)) ∧
          iSupProjection M
            (fun v : s ↦ (v : M.toStarSubalgebra) * star (v : M.toStarSubalgebra))
            (fun v ↦ (hs v.1 v.2).1.isStarProjection_mul_star_self) = 1 := by
  obtain ⟨p, hp, hpmin, _⟩ := hM.exists_minimal_abelian_projection hI
  obtain ⟨s, hps, hs, horth, hsup⟩ :=
    hM.exists_orthogonal_partial_isometries_of_minimal_projection hpmin
  refine ⟨p, hp, hpmin, s, hps, hs, horth, ?_, hsup⟩
  intro v hv
  have heq : MurrayVonNeumannEquivalent p (v * star v) :=
    ⟨hp.1, (hs v hv).1.isStarProjection_mul_star_self,
    v, (hs v hv).1, (hs v hv).2, rfl⟩
  have habel := hp.of_equivalent heq
  have hnonzero := heq.ne_zero_iff.mp hpmin.2.1
  exact ⟨habel, habel.isMinimalStarProjection_of_isFactor hnonzero hM⟩

end VonNeumannAlgebra
