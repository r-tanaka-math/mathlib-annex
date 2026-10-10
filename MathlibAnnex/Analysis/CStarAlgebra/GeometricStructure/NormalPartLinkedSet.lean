/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectivization
import MathlibAnnex.Topology.ClosureSpace.LinkedSet

/-!
# The two families of maximal linked sets in a normal part

The sets below live in the already constructed normal part and use the existing
`ClosureSpace.IsLinkedSet` and order-theoretic `Maximal`. The short coordinate
argument is specialized to two copies of THE SAME projective space. It does
not assert the false statement that all rows and columns of an arbitrary
nonempty product are maximal when just one factor is a singleton.
In dimension one both families consist of the same whole normal part.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- The literal normal-part subset with a fixed projective source. -/
def normalPartSourceFiber (p : ℙ ℂ H) : Set (normalPart S) :=
  {I | ((normalPartProjectivizationEquiv S hS).symm I).1 = p}

/-- The literal normal-part subset with a fixed projective target. -/
def normalPartTargetFiber (q : ℙ ℂ H) : Set (normalPart S) :=
  {I | ((normalPartProjectivizationEquiv S hS).symm I).2 = q}

@[simp]
theorem mem_normalPartSourceFiber_equiv (p : ℙ ℂ H) (r : (ℙ ℂ H) × (ℙ ℂ H)) :
    normalPartProjectivizationEquiv S hS r ∈ normalPartSourceFiber S hS p ↔ r.1 = p := by
  simp only [normalPartSourceFiber, Set.mem_setOf_eq, Equiv.symm_apply_apply]

@[simp]
theorem mem_normalPartTargetFiber_equiv (q : ℙ ℂ H) (r : (ℙ ℂ H) × (ℙ ℂ H)) :
    normalPartProjectivizationEquiv S hS r ∈ normalPartTargetFiber S hS q ↔ r.2 = q := by
  simp only [normalPartTargetFiber, Set.mem_setOf_eq, Equiv.symm_apply_apply]

/-- The source fiber in the original nonzero-vector presentation. -/
@[simp]
theorem mem_normalPartSourceFiber_point (p : ℙ ℂ H) (x y : H)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    normalPartPoint S hS x y hx hy ∈ normalPartSourceFiber S hS p ↔
      Projectivization.mk ℂ x hx = p := by
  simp only [normalPartSourceFiber, Set.mem_setOf_eq, normalPartProjectivizationEquiv_symm_point]

@[simp]
theorem mem_normalPartTargetFiber_point (q : ℙ ℂ H) (x y : H)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    normalPartPoint S hS x y hx hy ∈ normalPartTargetFiber S hS q ↔
      Projectivization.mk ℂ y hy = q := by
  simp only [normalPartTargetFiber, Set.mem_setOf_eq, normalPartProjectivizationEquiv_symm_point]

/-- Every source fiber is pairwise linked for the inherited closure. -/
theorem isLinkedSet_normalPartSourceFiber (p : ℙ ℂ H) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet
      (normalPartSourceFiber S hS p) := by
  intro I hI J hJ
  have h := (linked_normalPartProjectivizationEquiv_iff S hS
    ((normalPartProjectivizationEquiv S hS).symm I)
    ((normalPartProjectivizationEquiv S hS).symm J)).2 (Or.inl (hI.trans hJ.symm))
  simpa only [Equiv.apply_symm_apply] using h

/-- Every target fiber is pairwise linked as well. -/
theorem isLinkedSet_normalPartTargetFiber (q : ℙ ℂ H) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet
      (normalPartTargetFiber S hS q) := by
  intro I hI J hJ
  have h := (linked_normalPartProjectivizationEquiv_iff S hS
    ((normalPartProjectivizationEquiv S hS).symm I)
    ((normalPartProjectivizationEquiv S hS).symm J)).2 (Or.inr (hI.trans hJ.symm))
  simpa only [Equiv.apply_symm_apply] using h

/-- Every nonempty linked set is contained in one of the two literal fibers. -/
theorem subset_normalPartSourceFiber_or_targetFiber_of_isLinkedSet
    {L : Set (normalPart S)}
    (hL : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet L)
    (hne : L.Nonempty) :
    (∃ p : ℙ ℂ H, L ⊆ normalPartSourceFiber S hS p) ∨
      (∃ q : ℙ ℂ H, L ⊆ normalPartTargetFiber S hS q) := by
  classical
  let e := normalPartProjectivizationEquiv S hS
  obtain ⟨I, hI⟩ := hne
  have hlink (J K : normalPart S) (hJ : J ∈ L) (hK : K ∈ L) :
      (e.symm J).1 = (e.symm K).1 ∨ (e.symm J).2 = (e.symm K).2 := by
    apply (linked_normalPartProjectivizationEquiv_iff S hS (e.symm J) (e.symm K)).1
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (e (e.symm J)) (e (e.symm K))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact hL J hJ K hK
  by_cases hall : ∀ J ∈ L, (e.symm J).1 = (e.symm I).1
  · exact Or.inl ⟨(e.symm I).1, hall⟩
  · push_neg at hall
    obtain ⟨J, hJ, hJI⟩ := hall
    have hJI₂ : (e.symm J).2 = (e.symm I).2 := (hlink J I hJ hI).resolve_left hJI
    right
    refine ⟨(e.symm I).2, ?_⟩
    intro K hK
    change (e.symm K).2 = (e.symm I).2
    by_contra hKI₂
    have hKI₁ := (hlink K I hK hI).resolve_right hKI₂
    have hKJ₂ : (e.symm K).2 ≠ (e.symm J).2 := by
      intro hk
      exact hKI₂ (hk.trans hJI₂)
    have hKJ₁ := (hlink K J hK hJ).resolve_right hKJ₂
    exact hJI (hKJ₁.symm.trans hKI₁)

/-- Source fibers are maximal. The two tests `(p,p)` and `(p,r)` also
handle the singleton projective space, without assuming dimension at least two. -/
theorem maximal_isLinkedSet_normalPartSourceFiber (p : ℙ ℂ H) :
    Maximal
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet
      (normalPartSourceFiber S hS p) := by
  refine ⟨isLinkedSet_normalPartSourceFiber S hS p, ?_⟩
  intro L hL hsub I hI
  let e := normalPartProjectivizationEquiv S hS
  let r := (e.symm I).1
  let s := (e.symm I).2
  change r = p
  by_contra hr
  have hp₁ : e (p, p) ∈ L := hsub ((mem_normalPartSourceFiber_equiv S hS p (p, p)).2 rfl)
  have hp₂ : e (p, r) ∈ L := hsub ((mem_normalPartSourceFiber_equiv S hS p (p, r)).2 rfl)
  have h₁ : r = p ∨ s = p := by
    apply (linked_normalPartProjectivizationEquiv_iff S hS (e.symm I) (p, p)).1
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (e (e.symm I)) (e (p, p))
    rw [e.apply_symm_apply]
    exact hL I hI (e (p, p)) hp₁
  have h₂ : r = p ∨ s = r := by
    apply (linked_normalPartProjectivizationEquiv_iff S hS (e.symm I) (p, r)).1
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (e (e.symm I)) (e (p, r))
    rw [e.apply_symm_apply]
    exact hL I hI (e (p, r)) hp₂
  exact hr ((h₂.resolve_left hr).symm.trans (h₁.resolve_left hr))

/-- Target fibers are maximal, by the dual pair of coordinate tests. -/
theorem maximal_isLinkedSet_normalPartTargetFiber (q : ℙ ℂ H) :
    Maximal
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet
      (normalPartTargetFiber S hS q) := by
  refine ⟨isLinkedSet_normalPartTargetFiber S hS q, ?_⟩
  intro L hL hsub I hI
  let e := normalPartProjectivizationEquiv S hS
  let r := (e.symm I).1
  let s := (e.symm I).2
  change s = q
  by_contra hs
  have hp₁ : e (q, q) ∈ L := hsub ((mem_normalPartTargetFiber_equiv S hS q (q, q)).2 rfl)
  have hp₂ : e (s, q) ∈ L := hsub ((mem_normalPartTargetFiber_equiv S hS q (s, q)).2 rfl)
  have h₁ : r = q ∨ s = q := by
    apply (linked_normalPartProjectivizationEquiv_iff S hS (e.symm I) (q, q)).1
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (e (e.symm I)) (e (q, q))
    rw [e.apply_symm_apply]
    exact hL I hI (e (q, q)) hp₁
  have h₂ : r = s ∨ s = q := by
    apply (linked_normalPartProjectivizationEquiv_iff S hS (e.symm I) (s, q)).1
    change ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
      (e (e.symm I)) (e (s, q))
    rw [e.apply_symm_apply]
    exact hL I hI (e (s, q)) hp₂
  exact hs ((h₂.resolve_right hs).symm.trans (h₁.resolve_right hs))

/-- Lemma 6.13: the two fiber families exhaust all maximal R-sets. -/
theorem maximal_isLinkedSet_normalPart_iff (L : Set (normalPart S)) :
    Maximal
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).IsLinkedSet L ↔
      (∃ p : ℙ ℂ H, L = normalPartSourceFiber S hS p) ∨
      (∃ q : ℙ ℂ H, L = normalPartTargetFiber S hS q) := by
  classical
  constructor
  · intro hL
    letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero
      (NonUnitalStarSubalgebraClass.subtype S) hS.1
    let p : ℙ ℂ H := Classical.choice inferInstance
    have hne : L.Nonempty := by
      by_contra hne
      have hEmpty : L = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hsub : {normalPartProjectivizationEquiv S hS (p, p)} ⊆ L :=
        hL.2 (((NormedSpace.geometricStructureClosure ℂ S).subspace
          (normalPart S)).isLinkedSet_singleton _)
          (by rw [hEmpty]; exact Set.empty_subset _)
      have : normalPartProjectivizationEquiv S hS (p, p) ∈ L :=
        hsub (Set.mem_singleton_iff.mpr rfl)
      simpa only [hEmpty, Set.mem_empty_iff_false] using this
    rcases subset_normalPartSourceFiber_or_targetFiber_of_isLinkedSet S hS hL.1 hne with
      ⟨p, hp⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨p, hp.antisymm (hL.2 (isLinkedSet_normalPartSourceFiber S hS p) hp)⟩
    · exact Or.inr ⟨q, hq.antisymm (hL.2 (isLinkedSet_normalPartTargetFiber S hS q) hq)⟩
  · rintro (⟨p, rfl⟩ | ⟨q, rfl⟩)
    · exact maximal_isLinkedSet_normalPartSourceFiber S hS p
    · exact maximal_isLinkedSet_normalPartTargetFiber S hS q

/-- Opposite fibers meet in exactly the prescribed coefficient kernel. -/
theorem normalPartSourceFiber_inter_targetFiber (p q : ℙ ℂ H) :
    normalPartSourceFiber S hS p ∩ normalPartTargetFiber S hS q =
      {normalPartProjectivizationEquiv S hS (p, q)} := by
  ext I
  constructor
  · rintro ⟨hI₁, hI₂⟩
    apply Set.mem_singleton_iff.mpr
    apply (normalPartProjectivizationEquiv S hS).symm.injective
    change ((normalPartProjectivizationEquiv S hS).symm I).1 = p at hI₁
    change ((normalPartProjectivizationEquiv S hS).symm I).2 = q at hI₂
    rw [Equiv.symm_apply_apply]
    exact Prod.ext hI₁ hI₂
  · rintro rfl
    exact ⟨(mem_normalPartSourceFiber_equiv S hS p (p, q)).2 rfl,
      (mem_normalPartTargetFiber_equiv S hS q (p, q)).2 rfl⟩

private theorem subsingleton_projectivization_of_finrank_eq_one
    (hdim : Module.finrank ℂ H = 1) : Subsingleton (ℙ ℂ H) := by
  obtain ⟨z, hz, hspan⟩ := _root_.finrank_eq_one_iff'.1 hdim
  have hall (p : ℙ ℂ H) : p = Projectivization.mk ℂ z hz := by
    obtain ⟨a, ha⟩ := hspan p.rep
    calc
      p = Projectivization.mk ℂ p.rep p.rep_nonzero := p.mk_rep.symm
      _ = Projectivization.mk ℂ z hz :=
        (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2 ⟨a, ha⟩
  exact ⟨fun p q => (hall p).trans (hall q).symm⟩

/-- In dimension one every source fiber is the whole normal part. -/
theorem normalPartSourceFiber_eq_univ_of_finrank_eq_one
    (hdim : Module.finrank ℂ H = 1) (p : ℙ ℂ H) :
    normalPartSourceFiber S hS p = Set.univ := by
  letI := subsingleton_projectivization_of_finrank_eq_one hdim
  apply Set.eq_univ_of_forall
  intro I
  exact Subsingleton.elim _ _

/-- In dimension one the target family is the same whole-space family. -/
theorem normalPartTargetFiber_eq_univ_of_finrank_eq_one
    (hdim : Module.finrank ℂ H = 1) (q : ℙ ℂ H) :
    normalPartTargetFiber S hS q = Set.univ := by
  letI := subsingleton_projectivization_of_finrank_eq_one hdim
  apply Set.eq_univ_of_forall
  intro I
  exact Subsingleton.elim _ _

/-- The two descriptions coincide in dimension one; they are not falsely
counted as two different maximal sets. -/
theorem normalPartSourceFiber_eq_targetFiber_of_finrank_eq_one
    (hdim : Module.finrank ℂ H = 1) (p q : ℙ ℂ H) :
    normalPartSourceFiber S hS p = normalPartTargetFiber S hS q := by
  rw [normalPartSourceFiber_eq_univ_of_finrank_eq_one S hS hdim,
    normalPartTargetFiber_eq_univ_of_finrank_eq_one S hS hdim]

end MathlibAnnex.Analysis.CStarAlgebra
