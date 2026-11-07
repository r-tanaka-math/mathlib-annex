/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite witnesses for projective spans

The existing inductive projective span has finite character. Consequently a
bijection preserving and reflecting every finite-span incidence preserves all
span incidences. No topology, dimension assumption, or scalar map is involved.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

universe uK uL uV uW
variable {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
variable [DivisionRing K] [DivisionRing L]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]

namespace Subspace

/-- Every point of an algebraic projective span uses a finite subset of the
original generators. This includes the empty generating set. -/
theorem exists_finite_subset_of_mem_span {S : Set (ℙ K V)} {p : ℙ K V}
    (hp : p ∈ span S) :
    ∃ T : Set (ℙ K V), T.Finite ∧ T ⊆ S ∧ p ∈ span T := by
  induction hp using span_induction with
  | of_mem p hp =>
      exact ⟨{p}, finite_singleton p, singleton_subset_iff.mpr hp,
        subset_span {p} (by simp)⟩
  | add v w hv hw hvw hvS hwS ihv ihw =>
      obtain ⟨T, hTf, hTS, hvT⟩ := ihv
      obtain ⟨U, hUf, hUS, hwU⟩ := ihw
      exact ⟨T ∪ U, hTf.union hUf, union_subset hTS hUS,
        (span (T ∪ U)).mem_add v w hv hw hvw
          (span_le_span subset_union_left hvT) (span_le_span subset_union_right hwU)⟩

/-- Finite-character equivalence, with the actual finite generating subset. -/
theorem mem_span_iff_exists_finite_subset {S : Set (ℙ K V)} {p : ℙ K V} :
    p ∈ span S ↔ ∃ T : Set (ℙ K V), T.Finite ∧ T ⊆ S ∧ p ∈ span T := by
  refine ⟨exists_finite_subset_of_mem_span, ?_⟩
  rintro ⟨T, _, hTS, hp⟩
  exact span_le_span hTS hp

/-- Finite-span preservation implies arbitrary-span preservation, even for a
map that is not injective or surjective. -/
theorem mem_span_image_of_finite_span
    (f : ℙ K V → ℙ L W)
    (hf : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ span T → f p ∈ span (f '' T))
    {S : Set (ℙ K V)} {p : ℙ K V} (hp : p ∈ span S) :
    f p ∈ span (f '' S) := by
  obtain ⟨T, hTf, hTS, hpT⟩ := exists_finite_subset_of_mem_span hp
  exact span_le_span (image_mono hTS) (hf T hTf p hpT)

/-- The finite-incidence premise is inherited by the actual inverse bijection. -/
theorem finite_span_symm_iff
    (e : ℙ K V ≃ ℙ L W)
    (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ span T ↔ e p ∈ span (e '' T))
    (T : Set (ℙ L W)) (hT : T.Finite) (q : ℙ L W) :
    q ∈ span T ↔ e.symm q ∈ span (e.symm '' T) := by
  have h := he (e.symm '' T) (hT.image e.symm) (e.symm q)
  have himage : e '' (e.symm '' T) = T := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.apply_symm_apply] using hz
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩
  rw [e.apply_symm_apply, himage] at h
  exact h.symm

/-- A finite-incidence-preserving bijection preserves and reflects all spans. -/
theorem mem_span_image_iff_of_finite_span
    (e : ℙ K V ≃ ℙ L W)
    (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ span T ↔ e p ∈ span (e '' T))
    (S : Set (ℙ K V)) (p : ℙ K V) :
    p ∈ span S ↔ e p ∈ span (e '' S) := by
  constructor
  · exact mem_span_image_of_finite_span e (fun T hT p => (he T hT p).mp)
  · intro hp
    have h := mem_span_image_of_finite_span e.symm
      (fun T hT q => (finite_span_symm_iff e he T hT q).mp) hp
    have himage : e.symm '' (e '' S) = S := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        simpa only [e.symm_apply_apply] using hz
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    simpa only [e.symm_apply_apply, himage] using h

/-- Equality of the literal set images, not just a one-way span inclusion. -/
theorem image_span_eq_of_finite_span
    (e : ℙ K V ≃ ℙ L W)
    (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ span T ↔ e p ∈ span (e '' T))
    (S : Set (ℙ K V)) :
    e '' (span S : Set (ℙ K V)) = (span (e '' S) : Set (ℙ L W)) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_span_image_iff_of_finite_span e he S p).mp hp
  · intro hq
    change q ∈ span (e '' S) at hq
    exact ⟨e.symm q,
      (mem_span_image_iff_of_finite_span e he S (e.symm q)).mpr
        (by simpa only [e.apply_symm_apply] using hq), e.apply_symm_apply q⟩

/-- Representatives of the points generate exactly the algebraic submodule
corresponding to their projective span. The zero vector is retained. -/
theorem submodule_span_eq_span_rep_image (S : Set (ℙ K V)) :
    submodule (span S) = Submodule.span K (Projectivization.rep '' S) := by
  apply le_antisymm
  · have hle : span S ≤ (Submodule.span K (Projectivization.rep '' S)).projectivization := by
      apply span_le_subspace_iff.mpr
      intro p hp
      change p ∈ (Submodule.span K (Projectivization.rep '' S)).projectivization
      rw [← p.mk_rep, Submodule.mk_mem_projectivization_iff]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    exact (submodule.monotone hle).trans_eq
      (submodule.apply_symm_apply (Submodule.span K (Projectivization.rep '' S)))
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    apply (mem_submodule_iff _ p.rep_nonzero).mpr
    change Projectivization.mk K p.rep p.rep_nonzero ∈ (span S : Set (ℙ K V))
    simpa only [p.mk_rep] using subset_span S hp

/-- A projective point's one-dimensional submodule contains precisely that
projective point; this does not assume finite dimension of the ambient space. -/
theorem coe_projectivization_submodule (p : ℙ K V) :
    (p.submodule.projectivization : Set (ℙ K V)) = {p} := by
  ext q
  change q ∈ p.submodule.projectivization ↔ q = p
  rw [← q.mk_rep, Submodule.mk_mem_projectivization_iff,
    p.submodule_eq, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ((mk_eq_mk_iff' K q.rep p.rep q.rep_nonzero p.rep_nonzero).mpr ⟨a, ha⟩).trans
      p.mk_rep
  · intro h
    have hpq : q = p := q.mk_rep.symm.trans h
    exact ⟨1, by simp [hpq]⟩

end Subspace
end Projectivization
