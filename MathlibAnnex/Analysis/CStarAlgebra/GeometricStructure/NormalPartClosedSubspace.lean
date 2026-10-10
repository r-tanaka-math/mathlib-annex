/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartProjectiveDimension
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Closed inverse subspaces from full normal-part continuity

Algebraic span, norm closure, and relative normal-part closure remain distinct.
Coefficient evaluation embeds a norm-closure limit into a relative closure of
an ARBITRARY fixed-slot family. In the target, the orthogonal residual of a
closed subspace is tested using original-algebra one-vector transitivity.
No rank-one operator is asserted to lie in the algebra. The final statements
require full forward closure continuity in addition to a finite homeomorphism,
and conclude closedness of inverse images only. They do not use a semilinear lift.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- A norm limit in an algebraic submodule gives a point in the relative
closure of its whole fixed-target family. The family need not be finite. -/
theorem normalPartProjectivizationEquiv_mk_mem_closure_fixed_target
    (M : Submodule ℂ H) (x : H) (hx : x ≠ 0) (q : ℙ ℂ H)
    (hxM : x ∈ _root_.closure (M : Set H)) :
    normalPartProjectivizationEquiv S hS (Projectivization.mk ℂ x hx, q) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun p => normalPartProjectivizationEquiv S hS (p, q)) ''
          (M.projectivization : Set (ℙ ℂ H))) := by
  have point_eq (z : H) (hz : z ≠ 0) :
      normalPartProjectivizationEquiv S hS (Projectivization.mk ℂ z hz, q) =
        normalPartPoint S hS z q.rep hz q.rep_nonzero := by
    simpa only [Projectivization.mk_rep] using
      normalPartProjectivizationEquiv_mk S hS z q.rep hz q.rep_nonzero
  apply (mem_normalPart_closure_iff S _ _).mpr
  intro a ha
  have hM : (M : Set H) ⊆ {z : H | inner ℂ q.rep ((a : H →L[ℂ] H) z) = 0} := by
    intro z hz
    by_cases hz0 : z = 0
    · simp only [hz0, map_zero, inner_zero_right, Set.mem_setOf_eq]
    · have hm : Projectivization.mk ℂ z hz0 ∈ M.projectivization :=
        (Submodule.mk_mem_projectivization_iff M hz0).mpr hz
      have h := ha _ ⟨Projectivization.mk ℂ z hz0, hm, rfl⟩
      dsimp only at h
      rw [point_eq z hz0] at h
      exact h
  have hclosed : IsClosed {z : H | inner ℂ q.rep ((a : H →L[ℂ] H) z) = 0} :=
    isClosed_eq (continuous_const.inner (a : H →L[ℂ] H).continuous) continuous_const
  have h := (_root_.closure_minimal hM hclosed) hxM
  rw [point_eq x hx]
  exact h

/-- The varying target is conjugate-linear, but still norm continuous.
No chosen projective representative is assumed to depend continuously on a ray. -/
theorem normalPartProjectivizationEquiv_mk_mem_closure_fixed_source
    (M : Submodule ℂ H) (p : ℙ ℂ H) (y : H) (hy : y ≠ 0)
    (hyM : y ∈ _root_.closure (M : Set H)) :
    normalPartProjectivizationEquiv S hS (p, Projectivization.mk ℂ y hy) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun q => normalPartProjectivizationEquiv S hS (p, q)) ''
          (M.projectivization : Set (ℙ ℂ H))) := by
  have point_eq (z : H) (hz : z ≠ 0) :
      normalPartProjectivizationEquiv S hS (p, Projectivization.mk ℂ z hz) =
        normalPartPoint S hS p.rep z p.rep_nonzero hz := by
    simpa only [Projectivization.mk_rep] using
      normalPartProjectivizationEquiv_mk S hS p.rep z p.rep_nonzero hz
  apply (mem_normalPart_closure_iff S _ _).mpr
  intro a ha
  have hM : (M : Set H) ⊆ {z : H | inner ℂ z ((a : H →L[ℂ] H) p.rep) = 0} := by
    intro z hz
    by_cases hz0 : z = 0
    · simp only [hz0, inner_zero_left, Set.mem_setOf_eq]
    · have hm : Projectivization.mk ℂ z hz0 ∈ M.projectivization :=
        (Submodule.mk_mem_projectivization_iff M hz0).mpr hz
      have h := ha _ ⟨Projectivization.mk ℂ z hz0, hm, rfl⟩
      dsimp only at h
      rw [point_eq z hz0] at h
      exact h
  have hclosed : IsClosed {z : H | inner ℂ z ((a : H →L[ℂ] H) p.rep) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have h := (_root_.closure_minimal hM hclosed) hyM
  rw [point_eq y hy]
  exact h

/-- In a closed target subspace, relative closure adds no new source ray
within a fixed-target fiber. The test is the star of an element of S obtained
by one-vector transitivity, not an ambient rank-one assumed to belong to S. -/
theorem mem_projectivization_of_mem_normalPart_closure_fixed_target
    (N : Submodule ℂ H) (hN : IsClosed (N : Set H)) (p q : ℙ ℂ H)
    (h : normalPartProjectivizationEquiv S hS (p, q) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun r => normalPartProjectivizationEquiv S hS (r, q)) ''
          (N.projectivization : Set (ℙ ℂ H)))) : p ∈ N.projectivization := by
  letI : CompleteSpace N := hN.completeSpace_coe
  let r : H := p.rep - N.starProjection p.rep
  obtain ⟨a, ha⟩ := NonUnitalCStarRepresentation.apply_surjective_of_isIrreducible
    (NonUnitalStarSubalgebraClass.subtype S) hS q.rep_nonzero r
  change (a : H →L[ℂ] H) q.rep = r at ha
  have hz := (mem_normalPart_closure_iff S _ _).mp h (star a) (by
    rintro I ⟨s, hs, rfl⟩
    have hsN : s.rep ∈ N :=
      (Submodule.mk_mem_projectivization_iff N s.rep_nonzero).mp
        (by
          rw [Projectivization.mk_rep]
          change s ∈ (N.projectivization : Set (ℙ ℂ H))
          exact hs)
    change inner ℂ q.rep ((a : H →L[ℂ] H).adjoint s.rep) = 0
    rw [ContinuousLinearMap.adjoint_inner_right, ha]
    exact Submodule.starProjection_inner_eq_zero (K := N) p.rep s.rep hsN)
  change inner ℂ q.rep ((a : H →L[ℂ] H).adjoint p.rep) = 0 at hz
  rw [ContinuousLinearMap.adjoint_inner_right, ha] at hz
  have hrproj : inner ℂ r (N.starProjection p.rep) = 0 :=
    Submodule.starProjection_inner_eq_zero (K := N) p.rep _ (N.starProjection_apply_mem _)
  have hrr : inner ℂ r r = 0 := by
    change inner ℂ r (p.rep - N.starProjection p.rep) = 0
    rw [inner_sub_right, hz, hrproj, sub_self]
  have hr0 : r = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hrr
  have hpN : p.rep ∈ N := by
    have heq : p.rep = N.starProjection p.rep := sub_eq_zero.mp hr0
    rw [heq]
    exact N.starProjection_apply_mem _
  simpa only [Projectivization.mk_rep] using
    (Submodule.mk_mem_projectivization_iff N p.rep_nonzero).mpr hpN

/-- The fixed-source version uses the original interpolant, with the zero
condition in the conjugate-linear target slot kept in its correct direction. -/
theorem mem_projectivization_of_mem_normalPart_closure_fixed_source
    (N : Submodule ℂ H) (hN : IsClosed (N : Set H)) (p q : ℙ ℂ H)
    (h : normalPartProjectivizationEquiv S hS (p, q) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((fun r => normalPartProjectivizationEquiv S hS (p, r)) ''
          (N.projectivization : Set (ℙ ℂ H)))) : q ∈ N.projectivization := by
  letI : CompleteSpace N := hN.completeSpace_coe
  let r : H := q.rep - N.starProjection q.rep
  have hr : r ∈ Nᗮ := Submodule.sub_starProjection_mem_orthogonal (K := N) q.rep
  obtain ⟨a, ha⟩ := NonUnitalCStarRepresentation.apply_surjective_of_isIrreducible
    (NonUnitalStarSubalgebraClass.subtype S) hS p.rep_nonzero r
  change (a : H →L[ℂ] H) p.rep = r at ha
  have hz := (mem_normalPart_closure_iff S _ _).mp h a (by
    rintro I ⟨s, hs, rfl⟩
    have hsN : s.rep ∈ N :=
      (Submodule.mk_mem_projectivization_iff N s.rep_nonzero).mp
        (by
          rw [Projectivization.mk_rep]
          change s ∈ (N.projectivization : Set (ℙ ℂ H))
          exact hs)
    change inner ℂ s.rep ((a : H →L[ℂ] H) p.rep) = 0
    rw [ha]
    exact hr s.rep hsN)
  change inner ℂ q.rep ((a : H →L[ℂ] H) p.rep) = 0 at hz
  rw [ha] at hz
  have hrr : inner ℂ r r = 0 := by
    change inner ℂ (q.rep - N.starProjection q.rep) r = 0
    rw [inner_sub_left, hz, hr _ (N.starProjection_apply_mem _), sub_self]
  have hr0 : r = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hrr
  have hqN : q.rep ∈ N := by
    have heq : q.rep = N.starProjection q.rep := sub_eq_zero.mp hr0
    rw [heq]
    exact N.starProjection_apply_mem _
  simpa only [Projectivization.mk_rep] using
    (Submodule.mk_mem_projectivization_iff N q.rep_nonzero).mpr hqN

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (T : Set (K →L[ℂ] K))]
variable (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
variable (e : ClosureSpace.FiniteHomeomorph
  ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
  ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)))

/-- A direct first-factor formula and FULL forward continuity make inverse
images of norm-closed subspaces norm closed. No inverse continuity is used. -/
theorem isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_first_factor
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (hf : ∀ s : Set (ℙ ℂ H), s.Finite → ∀ p,
      p ∈ Projectivization.Subspace.span s ↔
        f p ∈ Projectivization.Subspace.span (f '' s))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((Projectivization.submoduleOrderIsoOfFiniteSpan f hf).symm N : Set H) := by
  let M := (Projectivization.submoduleOrderIsoOfFiniteSpan f hf).symm N
  have hclosed : _root_.closure (M : Set H) ⊆ (M : Set H) := by
    intro x hx
    by_cases hx0 : x = 0
    · change x ∈ M
      rw [hx0]
      exact M.zero_mem
    let p := Projectivization.mk ℂ x hx0
    let D := (fun r => normalPartProjectivizationEquiv S hS (r, p)) ''
      (M.projectivization : Set (ℙ ℂ H))
    let E := (fun r => normalPartProjectivizationEquiv T hT (r, g p)) ''
      (N.projectivization : Set (ℙ ℂ K))
    have hmem : normalPartProjectivizationEquiv S hS (p, p) ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D :=
      normalPartProjectivizationEquiv_mk_mem_closure_fixed_target S hS M x hx0 p hx
    have himage : e.toEquiv '' D ⊆ E := by
      rintro J ⟨I, ⟨r, hr, rfl⟩, rfl⟩
      have hrM : r.rep ∈ M :=
        (Submodule.mk_mem_projectivization_iff M r.rep_nonzero).mp
          (by
            rw [Projectivization.mk_rep]
            change r ∈ (M.projectivization : Set (ℙ ℂ H))
            exact hr)
      have hfr : f r ∈ N.projectivization := by
        simpa only [Projectivization.mk_rep] using
          (Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff
            f hf N r.rep r.rep_nonzero).mp hrM
      exact ⟨f r, hfr, (he (r, p)).symm⟩
    have htarget := hcont D ⟨normalPartProjectivizationEquiv S hS (p, p), hmem, rfl⟩
    rw [he (p, p)] at htarget
    have htarget' :=
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure_mono
        himage htarget
    have hfp : f p ∈ N.projectivization :=
      mem_projectivization_of_mem_normalPart_closure_fixed_target T hT N hN (f p) (g p)
        htarget'
    exact (Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff f hf N x hx0).mpr hfp
  have heq : _root_.closure (M : Set H) = (M : Set H) :=
    hclosed.antisymm _root_.subset_closure
  change IsClosed (M : Set H)
  rw [← heq]
  exact isClosed_closure

/-- The direct second-factor formula uses target-coefficient continuity and
the other one-vector separation; it is not deduced from finite continuity. -/
theorem isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_second_factor
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (hg : ∀ s : Set (ℙ ℂ H), s.Finite → ∀ p,
      p ∈ Projectivization.Subspace.span s ↔
        g p ∈ Projectivization.Subspace.span (g '' s))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((Projectivization.submoduleOrderIsoOfFiniteSpan g hg).symm N : Set H) := by
  let M := (Projectivization.submoduleOrderIsoOfFiniteSpan g hg).symm N
  have hclosed : _root_.closure (M : Set H) ⊆ (M : Set H) := by
    intro x hx
    by_cases hx0 : x = 0
    · change x ∈ M
      rw [hx0]
      exact M.zero_mem
    let p := Projectivization.mk ℂ x hx0
    let D := (fun r => normalPartProjectivizationEquiv S hS (p, r)) ''
      (M.projectivization : Set (ℙ ℂ H))
    let E := (fun r => normalPartProjectivizationEquiv T hT (f p, r)) ''
      (N.projectivization : Set (ℙ ℂ K))
    have hmem : normalPartProjectivizationEquiv S hS (p, p) ∈
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D :=
      normalPartProjectivizationEquiv_mk_mem_closure_fixed_source S hS M p x hx0 hx
    have himage : e.toEquiv '' D ⊆ E := by
      rintro J ⟨I, ⟨r, hr, rfl⟩, rfl⟩
      have hrM : r.rep ∈ M :=
        (Submodule.mk_mem_projectivization_iff M r.rep_nonzero).mp
          (by
            rw [Projectivization.mk_rep]
            change r ∈ (M.projectivization : Set (ℙ ℂ H))
            exact hr)
      have hgr : g r ∈ N.projectivization := by
        simpa only [Projectivization.mk_rep] using
          (Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff
            g hg N r.rep r.rep_nonzero).mp hrM
      exact ⟨g r, hgr, (he (p, r)).symm⟩
    have htarget := hcont D ⟨normalPartProjectivizationEquiv S hS (p, p), hmem, rfl⟩
    rw [he (p, p)] at htarget
    have htarget' :=
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure_mono
        himage htarget
    have hgp : g p ∈ N.projectivization :=
      mem_projectivization_of_mem_normalPart_closure_fixed_source T hT N hN (f p) (g p)
        htarget'
    exact (Projectivization.mem_symm_submoduleOrderIsoOfFiniteSpan_iff g hg N x hx0).mpr hgp
  have heq : _root_.closure (M : Set H) = (M : Set H) :=
    hclosed.antisymm _root_.subset_closure
  change IsClosed (M : Set H)
  rw [← heq]
  exact isClosed_closure

/-- Postcomposing with the existing FULL star homeomorphism preserves the
extra full continuity assumption when correcting a global swap. -/
theorem continuous_normalPartFiniteHomeomorphSwap
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartFiniteHomeomorphSwap S T hT e).toEquiv :=
  (normalPartStarHomeomorph T hT).continuous_toFun.comp hcont

/-- Both ACTUAL selected factor order maps have norm-closed inverse images
under full forward continuity, in either of the two global orientations. -/
theorem isClosed_symm_normalPart_submodule_order_isos
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartFirstSubmoduleOrderIso S T hS hT e).symm N : Set H) ∧
      IsClosed ((normalPartSecondSubmoduleOrderIso S T hS hT e).symm N : Set H) := by
  let f := normalPartProjectiveFirstFactor S T hS hT e
  let g := normalPartProjectiveSecondFactor S T hS hT e
  have hf : ∀ s : Set (ℙ ℂ H), s.Finite → ∀ p,
      p ∈ Projectivization.Subspace.span s ↔ f p ∈ Projectivization.Subspace.span (f '' s) :=
    fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).1 s hs p).symm
  have hg : ∀ s : Set (ℙ ℂ H), s.Finite → ∀ p,
      p ∈ Projectivization.Subspace.span s ↔ g p ∈ Projectivization.Subspace.span (g '' s) :=
    fun s hs p => ((normalPart_projective_factors_spec S T hS hT e).2.1 s hs p).symm
  rcases (normalPart_projective_factors_spec S T hS hT e).2.2 with he | he
  · exact ⟨isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_first_factor
        S hS T hT e f g hf he hcont N hN,
      isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_second_factor
        S hS T hT e f g hg he hcont N hN⟩
  · let e' := normalPartFiniteHomeomorphSwap S T hT e
    have he' := normalPartFiniteHomeomorphSwap_projectivization S T hS hT e f g he
    have hc' := continuous_normalPartFiniteHomeomorphSwap S T hT e hcont
    exact ⟨isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_first_factor
        S hS T hT e' f g hf he' hc' N hN,
      isClosed_symm_submoduleOrderIsoOfFiniteSpan_of_normalPart_second_factor
        S hS T hT e' f g hg he' hc' N hN⟩

/-- First selected order map, exposed separately for downstream closed-hyperplane arguments. -/
theorem isClosed_symm_normalPartFirstSubmoduleOrderIso
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartFirstSubmoduleOrderIso S T hS hT e).symm N : Set H) :=
  (isClosed_symm_normalPart_submodule_order_isos S hS T hT e hcont N hN).1

/-- Second selected order map; the same original finite homeomorphism is used. -/
theorem isClosed_symm_normalPartSecondSubmoduleOrderIso
    (hcont : ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) e.toEquiv)
    (N : Submodule ℂ K) (hN : IsClosed (N : Set K)) :
    IsClosed ((normalPartSecondSubmoduleOrderIso S T hS hT e).symm N : Set H) :=
  (isClosed_symm_normalPart_submodule_order_isos S hS T hT e hcont N hN).2

end MathlibAnnex.Analysis.CStarAlgebra
