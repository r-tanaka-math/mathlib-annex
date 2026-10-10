/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.AnnihilatorExtreme
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.ExtremeKernel
import MathlibAnnex.Topology.ClosureSpace.HullKernelPreimage
import MathlibAnnex.Topology.ClosureSpace.Induced

/-!
# Geometric structure spaces under a surjective C-star homomorphism

The points are the existing general geometric structure spaces. The inverse
family inclusion descends an arbitrary extreme functional through the FULL
annihilator equivalence. The target is the actual subspace of kernel-containing
points, not a redefined C-star structure space.

The elementary subfamily-to-subspace identification below is specialized to
these two C-star families. It is not a second generic subfamily construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Metric
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder B] [StarOrderedRing B]
variable [Nontrivial A] [Nontrivial B]
variable (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)

private def preimageContinuousMap (q : A →⋆ₙₐ[ℂ] B) : A →L[ℂ] B :=
  LinearMap.mkContinuous
    { toFun := q, map_add' := map_add q, map_smul' := map_smul q }
    1 (fun a => by
      change ‖q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le q a)

include hq in
/-- BOTH directions of the actual GSS family comparison. -/
theorem preimageFamily_geometricStructureFamily_eq :
    ClosureSpace.HullKernel.preimageFamily q (NormedSpace.geometricStructureFamily ℂ B) =
      {J : Set A | J ∈ NormedSpace.geometricStructureFamily ℂ A ∧
        ((preimageContinuousMap q).ker : Set A) ⊆ J} := by
  ext J
  constructor
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨f, hf, rfl⟩ :=
      (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall L).1 hL
    refine ⟨?_, ?_⟩
    · apply (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall _).2
      exact ⟨f.comp (preimageContinuousMap q),
        comp_mem_extremePoints_dual_closedBall_of_surjective q hq hf, rfl⟩
    · intro a ha
      change f (q a) = 0
      rw [show q a = 0 from ha, map_zero]
  · rintro ⟨hJ, hK⟩
    obtain ⟨g, hg, hgJ⟩ :=
      (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall J).1 hJ
    have hga : g ∈ (preimageContinuousMap q).ker.strongDualAnnihilator := by
      intro a ha
      have hmem := hK ha
      rw [← hgJ] at hmem
      exact hmem
    let ag : (preimageContinuousMap q).ker.strongDualAnnihilator := ⟨g, hga⟩
    let f := (surjectiveDualLinearIsometryEquiv q hq).symm ag
    have hfg : f.comp (preimageContinuousMap q) = g := by
      ext a
      exact surjectiveDualLinearIsometryEquiv_symm_apply_image q hq ag a
    have hf : f ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ := by
      have hp : f.comp (preimageContinuousMap q) ∈
          (closedBall (0 : StrongDual ℂ A) 1).extremePoints ℝ ↔
          f ∈ (closedBall (0 : StrongDual ℂ B) 1).extremePoints ℝ :=
        comp_mem_extremePoints_dual_closedBall_iff_of_surjective q hq f
      apply hp.mp
      rw [hfg]
      exact hg
    refine ⟨(f.ker : Set B), ?_, ?_⟩
    · exact (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall _).2
        ⟨f, hf, rfl⟩
    · calc
        q ⁻¹' (f.ker : Set B) = ((f.comp (preimageContinuousMap q)).ker : Set A) := rfl
        _ = (g.ker : Set A) := congrArg (fun k : StrongDual ℂ A => (k.ker : Set A)) hfg
        _ = J := hgJ

/-- The preimage-family type is the actual kernel-containing SUBTYPE of S(A). -/
def preimageFamilyKernelHullEquiv :
    ClosureSpace.HullKernel.preimageFamily q (NormedSpace.geometricStructureFamily ℂ B) ≃
      ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
        ((preimageContinuousMap q).ker : Set A) where
  toFun J := by
    have heq := congrArg (fun F : Set (Set A) => J.val ∈ F)
      (preimageFamily_geometricStructureFamily_eq q hq)
    have h := Eq.mp heq J.property
    exact ⟨⟨J.val, h.1⟩, h.2⟩
  invFun J := by
    refine ⟨J.val.val, ?_⟩
    rw [preimageFamily_geometricStructureFamily_eq q hq]
    exact ⟨J.val.property, J.property⟩
  left_inv J := Subtype.ext rfl
  right_inv J := by apply Subtype.ext; exact Subtype.ext rfl

@[simp]
theorem preimageFamilyKernelHullEquiv_val
    (J : ClosureSpace.HullKernel.preimageFamily q (NormedSpace.geometricStructureFamily ℂ B)) :
    (preimageFamilyKernelHullEquiv q hq J).val.val = J.val := rfl

/-- All-subset closure preservation into the actual subspace of S(A).
No finite-union/topologizability hypothesis is used. -/
theorem image_closure_preimageFamilyKernelHullEquiv
    (S : Set (ClosureSpace.HullKernel.preimageFamily q
      (NormedSpace.geometricStructureFamily ℂ B))) :
    preimageFamilyKernelHullEquiv q hq ''
        (ClosureSpace.HullKernel.space _
          (ClosureSpace.HullKernel.univ_notMem_preimageFamily q hq _
            (NormedSpace.univ_notMem_geometricStructureFamily ℂ B))).closure S =
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
          ((preimageContinuousMap q).ker : Set A))).closure
            (preimageFamilyKernelHullEquiv q hq '' S) := by
  let e := preimageFamilyKernelHullEquiv q hq
  ext I
  obtain ⟨J, rfl⟩ := e.surjective I
  constructor
  · rintro ⟨J', hJ', heq⟩
    have hJJ : J' = J := e.injective heq
    subst J'
    change ClosureSpace.HullKernel.kernel _
      (Subtype.val '' (e '' S)) ⊆ (e J).val.val
    change ClosureSpace.HullKernel.kernel _ S ⊆ J.val at hJ'
    intro a ha
    apply hJ'
    intro L hL
    exact ha (e L).val ⟨e L, ⟨L, hL, rfl⟩, rfl⟩
  · intro hJ
    change ClosureSpace.HullKernel.kernel _ (Subtype.val '' (e '' S)) ⊆
      (e J).val.val at hJ
    refine ⟨J, ?_, rfl⟩
    change ClosureSpace.HullKernel.kernel _ S ⊆ J.val
    intro a ha
    apply hJ
    rintro L ⟨M, ⟨N, hN, rfl⟩, rfl⟩
    exact ha N hN

/-- The second, subfamily-to-subspace stage of the comparison. -/
def preimageFamilyKernelHullHomeomorph :
    ClosureSpace.Homeomorph
      (ClosureSpace.HullKernel.space _
        (ClosureSpace.HullKernel.univ_notMem_preimageFamily q hq _
          (NormedSpace.univ_notMem_geometricStructureFamily ℂ B)))
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
          ((preimageContinuousMap q).ker : Set A))) :=
  ClosureSpace.Homeomorph.ofImageClosure _ _ (preimageFamilyKernelHullEquiv q hq)
    (image_closure_preimageFamilyKernelHullEquiv q hq)

/-- The existing MAIN preimage homeomorphism followed by the actual subspace comparison. -/
def geometricStructurePreimageHomeomorph :
    ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ B)
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
          ((preimageContinuousMap q).ker : Set A))) :=
  (ClosureSpace.HullKernel.homeomorphPreimage q hq
    (NormedSpace.geometricStructureFamily ℂ B)
    (NormedSpace.univ_notMem_geometricStructureFamily ℂ B)).trans
      (preimageFamilyKernelHullHomeomorph q hq)

/-- Every point is sent to its literal preimage, independently of functional choices. -/
@[simp]
theorem geometricStructurePreimageHomeomorph_val (J : NormedSpace.GeometricStructureSpace ℂ B) :
    ((geometricStructurePreimageHomeomorph q hq).toEquiv J).val.val = q ⁻¹' J.val := rfl

/-- Inverse set recovery in the original algebra. -/
theorem geometricStructurePreimageHomeomorph_symm_val
    (I : ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
      ((preimageContinuousMap q).ker : Set A)) :
    q ⁻¹' ((geometricStructurePreimageHomeomorph q hq).toEquiv.symm I).val = I.val.val := by
  have h := congrArg (fun J => J.val.val)
    ((geometricStructurePreimageHomeomorph q hq).toEquiv.apply_symm_apply I)
  exact h

/-- All closures, not only finite closures, are transported forward. -/
theorem image_closure_geometricStructurePreimageHomeomorph
    (S : Set (NormedSpace.GeometricStructureSpace ℂ B)) :
    (geometricStructurePreimageHomeomorph q hq).toEquiv ''
        (NormedSpace.geometricStructureClosure ℂ B).closure S =
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
          ((preimageContinuousMap q).ker : Set A))).closure
        ((geometricStructurePreimageHomeomorph q hq).toEquiv '' S) :=
  (geometricStructurePreimageHomeomorph q hq).image_closure S

/-- The inverse preserves arbitrary closures in the actual target subspace. -/
theorem image_closure_geometricStructurePreimageHomeomorph_symm
    (S : Set (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
      ((preimageContinuousMap q).ker : Set A))) :
    (geometricStructurePreimageHomeomorph q hq).toEquiv.symm ''
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          (ClosureSpace.HullKernel.hull (NormedSpace.geometricStructureFamily ℂ A)
            ((preimageContinuousMap q).ker : Set A))).closure S =
      (NormedSpace.geometricStructureClosure ℂ B).closure
        ((geometricStructurePreimageHomeomorph q hq).toEquiv.symm '' S) :=
  (geometricStructurePreimageHomeomorph q hq).symm.image_closure S

end MathlibAnnex.Analysis.CStarAlgebra
