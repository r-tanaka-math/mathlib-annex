/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveSpan

/-!
# Finite-span incidence of the actual projective factors

The hypotheses are an actual finite homeomorphism of the existing normal parts.
The factor formula comes from the existing coordinate decomposition, and its
incidence property is proved from the relative closure formulas. No assumed
semilinear lift, field automorphism, submodule order isomorphism, or continuity
on arbitrary subsets is used. Both orientations are treated, using the existing
full star homeomorphism to reduce the swapped case to the direct case.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (S : Set (H →L[ℂ] H))] [IsClosed (T : Set (K →L[ℂ] K))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

/-- Fixed target converts preservation of finite normal closures into
preservation and reflection of finite source-span incidence. -/
theorem mem_span_range_normalPart_projective_first_factor_iff
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    {ι : Type*} [Fintype ι] (p : ι → ℙ ℂ H) (r : ℙ ℂ H) :
    f r ∈ Projectivization.Subspace.span (Set.range fun i => f (p i)) ↔
      r ∈ Projectivization.Subspace.span (Set.range p) := by
  classical
  let a : ℙ ℂ H := r
  let D : Set (normalPart S) :=
    Set.range fun i => normalPartProjectivizationEquiv S hS (p i, a)
  let D' : Set (normalPart T) :=
    Set.range fun i => normalPartProjectivizationEquiv T hT (f (p i), g a)
  have him : e.toEquiv '' D = D' := by
    ext J
    constructor
    · rintro ⟨I, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (he (p i, a)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨normalPartProjectivizationEquiv S hS (p i, a), ⟨i, rfl⟩, he (p i, a)⟩
  have hs : normalPartProjectivizationEquiv S hS (r, a) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D ↔
        r ∈ Projectivization.Subspace.span (Set.range p) := by
    exact (mem_closure_range_normalPartProjectivizationEquiv_fixed_target_iff
      S hS p a (r, a)).trans ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have ht : normalPartProjectivizationEquiv T hT (f r, g a) ∈
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure D' ↔
        f r ∈ Projectivization.Subspace.span (Set.range fun i => f (p i)) := by
    exact (mem_closure_range_normalPartProjectivizationEquiv_fixed_target_iff
      T hT (fun i => f (p i)) (g a) (f r, g a)).trans
        ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hm := normalPart_finiteHomeomorph_mem_closure_image_iff S T e D
    (Set.finite_range _) (normalPartProjectivizationEquiv S hS (r, a))
  rw [him, he] at hm
  exact ht.symm.trans (hm.trans hs)

/-- Fixed source gives the target-span statement. Target conjugations were
already accounted for in the finite relative-closure theorem. -/
theorem mem_span_range_normalPart_projective_second_factor_iff
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    {ι : Type*} [Fintype ι] (p : ι → ℙ ℂ H) (r : ℙ ℂ H) :
    g r ∈ Projectivization.Subspace.span (Set.range fun i => g (p i)) ↔
      r ∈ Projectivization.Subspace.span (Set.range p) := by
  classical
  let a : ℙ ℂ H := r
  let D : Set (normalPart S) :=
    Set.range fun i => normalPartProjectivizationEquiv S hS (a, p i)
  let D' : Set (normalPart T) :=
    Set.range fun i => normalPartProjectivizationEquiv T hT (f a, g (p i))
  have him : e.toEquiv '' D = D' := by
    ext J
    constructor
    · rintro ⟨I, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (he (a, p i)).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨normalPartProjectivizationEquiv S hS (a, p i), ⟨i, rfl⟩, he (a, p i)⟩
  have hs : normalPartProjectivizationEquiv S hS (a, r) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D ↔
        r ∈ Projectivization.Subspace.span (Set.range p) := by
    exact (mem_closure_range_normalPartProjectivizationEquiv_fixed_source_iff
      S hS a p (a, r)).trans ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have ht : normalPartProjectivizationEquiv T hT (f a, g r) ∈
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure D' ↔
        g r ∈ Projectivization.Subspace.span (Set.range fun i => g (p i)) := by
    exact (mem_closure_range_normalPartProjectivizationEquiv_fixed_source_iff
      T hT (f a) (fun i => g (p i)) (f a, g r)).trans
        ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have hm := normalPart_finiteHomeomorph_mem_closure_image_iff S T e D
    (Set.finite_range _) (normalPartProjectivizationEquiv S hS (a, r))
  rw [him, he] at hm
  exact ht.symm.trans (hm.trans hs)

/-- Both factors preserve and reflect incidence with the span of every finite set. -/
theorem normalPart_projective_factors_preserve_finite_span
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2)) :
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      f p ∈ Projectivization.Subspace.span (f '' s) ↔
        p ∈ Projectivization.Subspace.span s) ∧
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      g p ∈ Projectivization.Subspace.span (g '' s) ↔
        p ∈ Projectivization.Subspace.span s) := by
  classical
  have ranges (s : Set (ℙ ℂ H)) (f : (ℙ ℂ H) ≃ (ℙ ℂ K)) :
      Set.range (fun x : s => f x.val) = f '' s := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro s hs p
    letI : Fintype s := hs.fintype
    have hr : Set.range (fun x : s => x.val) = s := by ext x; simp
    simpa only [hr, ranges] using
      mem_span_range_normalPart_projective_first_factor_iff S T hS hT e f g he
        (fun x : s => x.val) p
  · intro s hs p
    letI : Fintype s := hs.fintype
    have hr : Set.range (fun x : s => x.val) = s := by ext x; simp
    simpa only [hr, ranges] using
      mem_span_range_normalPart_projective_second_factor_iff S T hS hT e f g he
        (fun x : s => x.val) p

/-- The same incidence conclusion in the globally swapped orientation.
The swap is removed by a genuine existing homeomorphism, not by relabelling a map. -/
theorem normalPart_projective_swapped_factors_preserve_finite_span
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1)) :
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      f p ∈ Projectivization.Subspace.span (f '' s) ↔
        p ∈ Projectivization.Subspace.span s) ∧
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      g p ∈ Projectivization.Subspace.span (g '' s) ↔
        p ∈ Projectivization.Subspace.span s) :=
  normalPart_projective_factors_preserve_finite_span S T hS hT
    (normalPartFiniteHomeomorphSwap S T hT e) f g
    (normalPartFiniteHomeomorphSwap_projectivization S T hS hT e f g he)

/-- The unconditional geometric endpoint: the two factor equivalences and
both finite-incidence laws follow from the actual given finite homeomorphism. -/
theorem exists_normalPart_projective_factors_preserving_finite_span :
    ∃ f g : (ℙ ℂ H) ≃ (ℙ ℂ K),
      (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
        f p ∈ Projectivization.Subspace.span (f '' s) ↔
          p ∈ Projectivization.Subspace.span s) ∧
      (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
        g p ∈ Projectivization.Subspace.span (g '' s) ↔
          p ∈ Projectivization.Subspace.span s) ∧
      ((∀ p : (ℙ ℂ H) × (ℙ ℂ H),
        e.toEquiv (normalPartProjectivizationEquiv S hS p) =
          normalPartProjectivizationEquiv T hT (f p.1, g p.2)) ∨
       (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
        e.toEquiv (normalPartProjectivizationEquiv S hS p) =
          normalPartProjectivizationEquiv T hT (g p.2, f p.1))) := by
  rcases exists_normalPart_projective_factors_or_swapped S T hS hT e with
    ⟨f, g, hfg⟩ | ⟨f, g, hfg⟩
  · obtain ⟨hf, hg⟩ := normalPart_projective_factors_preserve_finite_span S T hS hT e f g hfg
    exact ⟨f, g, hf, hg, Or.inl hfg⟩
  · obtain ⟨hf, hg⟩ :=
      normalPart_projective_swapped_factors_preserve_finite_span S T hS hT e f g hfg
    exact ⟨f, g, hf, hg, Or.inr hfg⟩

/-- A selected first factor, chosen only after its existence and incidence laws were proved. -/
def normalPartProjectiveFirstFactor : (ℙ ℂ H) ≃ (ℙ ℂ K) :=
  Classical.choose (exists_normalPart_projective_factors_preserving_finite_span S T hS hT e)

/-- A selected second factor belonging to the same proved factorization. -/
def normalPartProjectiveSecondFactor : (ℙ ℂ H) ≃ (ℙ ℂ K) :=
  Classical.choose (Classical.choose_spec
    (exists_normalPart_projective_factors_preserving_finite_span S T hS hT e))

/-- The selected factor maps have the proved finite-span and orientation properties. -/
theorem normalPart_projective_factors_spec :
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      normalPartProjectiveFirstFactor S T hS hT e p ∈
          Projectivization.Subspace.span (normalPartProjectiveFirstFactor S T hS hT e '' s) ↔
        p ∈ Projectivization.Subspace.span s) ∧
    (∀ s : Set (ℙ ℂ H), s.Finite → ∀ p : ℙ ℂ H,
      normalPartProjectiveSecondFactor S T hS hT e p ∈
          Projectivization.Subspace.span (normalPartProjectiveSecondFactor S T hS hT e '' s) ↔
        p ∈ Projectivization.Subspace.span s) ∧
    ((∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT
          (normalPartProjectiveFirstFactor S T hS hT e p.1,
           normalPartProjectiveSecondFactor S T hS hT e p.2)) ∨
     (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT
          (normalPartProjectiveSecondFactor S T hS hT e p.2,
           normalPartProjectiveFirstFactor S T hS hT e p.1))) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_normalPart_projective_factors_preserving_finite_span S T hS hT e))

/-- Projective line incidence is the two-point specialization, not the input to the finite theorem. -/
theorem normalPart_projective_factors_pair_span_iff (p q r : ℙ ℂ H) :
    (normalPartProjectiveFirstFactor S T hS hT e r ∈
        Projectivization.Subspace.span
          {normalPartProjectiveFirstFactor S T hS hT e p,
           normalPartProjectiveFirstFactor S T hS hT e q} ↔
      r ∈ Projectivization.Subspace.span {p, q}) ∧
    (normalPartProjectiveSecondFactor S T hS hT e r ∈
        Projectivization.Subspace.span
          {normalPartProjectiveSecondFactor S T hS hT e p,
           normalPartProjectiveSecondFactor S T hS hT e q} ↔
      r ∈ Projectivization.Subspace.span {p, q}) := by
  obtain ⟨hf, hg, _⟩ := normalPart_projective_factors_spec S T hS hT e
  exact ⟨by simpa only [Set.image_pair] using hf {p, q} (Set.Finite.insert p (Set.finite_singleton q)) r,
    by simpa only [Set.image_pair] using hg {p, q} (Set.Finite.insert p (Set.finite_singleton q)) r⟩

/-- The selected inverse factors preserve and reflect finite incidence as well. -/
theorem normalPart_projective_factors_symm_span_iff
    (s : Set (ℙ ℂ K)) (hs : s.Finite) (p : ℙ ℂ K) :
    ((normalPartProjectiveFirstFactor S T hS hT e).symm p ∈
        Projectivization.Subspace.span
          ((normalPartProjectiveFirstFactor S T hS hT e).symm '' s) ↔
      p ∈ Projectivization.Subspace.span s) ∧
    ((normalPartProjectiveSecondFactor S T hS hT e).symm p ∈
        Projectivization.Subspace.span
          ((normalPartProjectiveSecondFactor S T hS hT e).symm '' s) ↔
      p ∈ Projectivization.Subspace.span s) := by
  obtain ⟨hf, hg, _⟩ := normalPart_projective_factors_spec S T hS hT e
  constructor
  · have h := hf ((normalPartProjectiveFirstFactor S T hS hT e).symm '' s)
      (hs.image _) ((normalPartProjectiveFirstFactor S T hS hT e).symm p)
    have hi : normalPartProjectiveFirstFactor S T hS hT e ''
        ((normalPartProjectiveFirstFactor S T hS hT e).symm '' s) = s := by
      ext q
      simp
    simpa only [Equiv.apply_symm_apply, hi] using h.symm
  · have h := hg ((normalPartProjectiveSecondFactor S T hS hT e).symm '' s)
      (hs.image _) ((normalPartProjectiveSecondFactor S T hS hT e).symm p)
    have hi : normalPartProjectiveSecondFactor S T hS hT e ''
        ((normalPartProjectiveSecondFactor S T hS hT e).symm '' s) = s := by
      ext q
      simp
    simpa only [Equiv.apply_symm_apply, hi] using h.symm

/-- The inverse of the original normal-part map has the matching global orientation. -/
theorem normalPart_projective_factors_inverse_formula :
    (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
        normalPartProjectivizationEquiv S hS
          ((normalPartProjectiveFirstFactor S T hS hT e).symm q.1,
           (normalPartProjectiveSecondFactor S T hS hT e).symm q.2)) ∨
    (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
        normalPartProjectivizationEquiv S hS
          ((normalPartProjectiveFirstFactor S T hS hT e).symm q.2,
           (normalPartProjectiveSecondFactor S T hS hT e).symm q.1)) := by
  rcases (normalPart_projective_factors_spec S T hS hT e).2.2 with h | h
  · exact Or.inl (normalPart_projective_inverse_of_factors S T hS hT e _ _ h)
  · exact Or.inr (normalPart_projective_inverse_of_swapped_factors S T hS hT e _ _ h)


/-- Forward and inverse formulas are in the same global orientation. -/
theorem normalPart_projective_factors_evaluation :
    let f := normalPartProjectiveFirstFactor S T hS hT e
    let g := normalPartProjectiveSecondFactor S T hS hT e
    ((∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2)) ∧
     (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
        normalPartProjectivizationEquiv S hS (f.symm q.1, g.symm q.2))) ∨
    ((∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1)) ∧
     (∀ q : (ℙ ℂ K) × (ℙ ℂ K),
      e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
        normalPartProjectivizationEquiv S hS (f.symm q.2, g.symm q.1))) := by
  dsimp only
  rcases (normalPart_projective_factors_spec S T hS hT e).2.2 with h | h
  · exact Or.inl ⟨h, normalPart_projective_inverse_of_factors S T hS hT e _ _ h⟩
  · exact Or.inr ⟨h, normalPart_projective_inverse_of_swapped_factors S T hS hT e _ _ h⟩

/-- Evaluation in the original coefficient kernels, with target conjugate-linearity intact.
The representatives are those of actual Mathlib projective points. -/
theorem normalPart_projective_factors_kernel_formula :
    let f := normalPartProjectiveFirstFactor S T hS hT e
    let g := normalPartProjectiveSecondFactor S T hS hT e
    (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      (e.toEquiv (normalPartProjectivizationEquiv S hS p)).val.val =
        {b : T | inner ℂ (g p.2).rep ((b : K →L[ℂ] K) (f p.1).rep) = 0}) ∨
    (∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      (e.toEquiv (normalPartProjectivizationEquiv S hS p)).val.val =
        {b : T | inner ℂ (f p.1).rep ((b : K →L[ℂ] K) (g p.2).rep) = 0}) := by
  dsimp only
  rcases (normalPart_projective_factors_spec S T hS hT e).2.2 with h | h
  · refine Or.inl fun p => ?_
    rw [h p, normalPartProjectivizationEquiv_val_val]
  · refine Or.inr fun p => ?_
    rw [h p, normalPartProjectivizationEquiv_val_val]

end MathlibAnnex.Analysis.CStarAlgebra
