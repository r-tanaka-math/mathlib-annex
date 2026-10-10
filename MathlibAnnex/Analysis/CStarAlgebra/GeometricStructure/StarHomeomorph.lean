/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.Normed.GeometricStructure.Preserver
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartLinkedSet
import MathlibAnnex.Topology.ClosureSpace.SubspaceMaps

/-!
# Star as a full geometric-structure homeomorphism

This proof uses the already proved general Birkhoff--James preserver theorem:
star preserves the norm, is conjugate-linear, and is an involution. Consequently
the image of every point belongs to the original face-defined GSS, and arbitrary
closures, not just finite closures, are preserved. The coefficient identity
then restricts this very homeomorphism to the normal part and exchanges the two
projective factors. No ordinary topology on the full GSS is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable (A : Type u) [NonUnitalCStarAlgebra A]

/-- Conjugating the scalar parameter proves orthogonality preservation. -/
theorem birkhoffJamesOrthogonal_star_iff (x y : A) :
    NormedSpace.BirkhoffJamesOrthogonal ℂ (star x) (star y) ↔
      NormedSpace.BirkhoffJamesOrthogonal ℂ x y := by
  constructor
  · intro h c
    have hc := h (star c)
    have hs : star (x + c • y) = star x + star c • star y := by simp only [star_add, star_smul]
    simpa only [← hs, norm_star] using hc
  · intro h c
    have hs : star (x + star c • y) = star x + c • star y := by
      simp only [star_add, star_smul, star_star]
    calc
      ‖star x‖ = ‖x‖ := norm_star x
      _ ≤ ‖x + star c • y‖ := h (star c)
      _ = ‖star x + c • star y‖ := by rw [← hs, norm_star]

/-- The actual star-image map on the original full geometric structure space.
This includes the empty GSS of the zero algebra. -/
def geometricStructureStarHomeomorph :
    ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ A) :=
  NormedSpace.geometricStructureHomeomorphOfBirkhoffJames ℂ ℂ
    (Equiv.Perm.star : Equiv.Perm A) (birkhoffJamesOrthogonal_star_iff A)

/-- The underlying set is literally the star image. -/
@[simp]
theorem geometricStructureStarHomeomorph_apply_val
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ((geometricStructureStarHomeomorph A).toEquiv I).val = star '' I.val := rfl

/-- Incidence can equivalently be tested by applying star to the element. -/
theorem mem_geometricStructureStarHomeomorph_iff
    (I : NormedSpace.GeometricStructureSpace ℂ A) (a : A) :
    a ∈ ((geometricStructureStarHomeomorph A).toEquiv I).val ↔ star a ∈ I.val := by
  rw [geometricStructureStarHomeomorph_apply_val]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa only [star_star] using hb
  · intro ha
    exact ⟨star a, ha, star_star a⟩

/-- The star-induced map is an involution on ACTUAL GSS points. -/
theorem geometricStructureStarHomeomorph_involutive :
    Function.Involutive (geometricStructureStarHomeomorph A).toEquiv := by
  intro I
  apply Subtype.ext
  simp only [geometricStructureStarHomeomorph_apply_val, Set.image_image,
    Function.comp_def, star_star]
  change id '' I.val = I.val
  exact Set.image_id _

@[simp]
theorem geometricStructureStarHomeomorph_symm_apply
    (I : NormedSpace.GeometricStructureSpace ℂ A) :
    (geometricStructureStarHomeomorph A).toEquiv.symm I =
      (geometricStructureStarHomeomorph A).toEquiv I := by
  have h := geometricStructureStarHomeomorph_involutive A
    ((geometricStructureStarHomeomorph A).toEquiv.symm I)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Full closure preservation, with no finiteness restriction on the set. -/
theorem image_closure_geometricStructureStarHomeomorph
    (D : Set (NormedSpace.GeometricStructureSpace ℂ A)) :
    (geometricStructureStarHomeomorph A).toEquiv ''
        (NormedSpace.geometricStructureClosure ℂ A).closure D =
      (NormedSpace.geometricStructureClosure ℂ A).closure
        ((geometricStructureStarHomeomorph A).toEquiv '' D) :=
  (geometricStructureStarHomeomorph A).image_closure D

variable {A}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Adjoint coefficient values are conjugated, but the zero condition is
unchanged. This identity does not require irreducibility or nonzero vectors. -/
theorem NonUnitalCStarRepresentation.star_image_ker_matrixCoefficient
    (pi : NonUnitalCStarRepresentation A H) (x y : H) :
    star '' ((pi.matrixCoefficient x y).ker : Set A) =
      ((pi.matrixCoefficient y x).ker : Set A) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    change pi.matrixCoefficient y x (star b) = 0
    rw [NonUnitalCStarRepresentation.matrixCoefficient_star]
    change star (pi.matrixCoefficient x y b) = 0
    rw [show pi.matrixCoefficient x y b = 0 from hb, star_zero]
  · intro ha
    refine ⟨star a, ?_, star_star a⟩
    change pi.matrixCoefficient x y (star a) = 0
    rw [NonUnitalCStarRepresentation.matrixCoefficient_star]
    rw [show pi.matrixCoefficient y x a = 0 from ha, star_zero]

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- The full-GSS map exchanges the source and target of a normal kernel. -/
@[simp]
theorem geometricStructureStarHomeomorph_restrictedMatrixCoefficientKernel
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (geometricStructureStarHomeomorph S).toEquiv
        (restrictedMatrixCoefficientKernel S hS x y hx hy) =
      restrictedMatrixCoefficientKernel S hS y x hy hx := by
  apply Subtype.ext
  exact NonUnitalCStarRepresentation.star_image_ker_matrixCoefficient
    (NonUnitalStarSubalgebraClass.subtype S) x y

include hS in
/-- The same full-GSS involution preserves and reflects normal membership. -/
theorem mem_normalPart_geometricStructureStarHomeomorph_iff
    (I : NormedSpace.GeometricStructureSpace ℂ S) :
    (geometricStructureStarHomeomorph S).toEquiv I ∈ normalPart S ↔ I ∈ normalPart S := by
  have forward (J : NormedSpace.GeometricStructureSpace ℂ S)
      (hJ : J ∈ normalPart S) :
      (geometricStructureStarHomeomorph S).toEquiv J ∈ normalPart S := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hJ
    have heq : J = restrictedMatrixCoefficientKernel S hS x y hx hy := Subtype.ext hxy.symm
    rw [heq, geometricStructureStarHomeomorph_restrictedMatrixCoefficientKernel]
    exact ⟨y, x, hy, hx, rfl⟩
  constructor
  · intro hI
    simpa only [geometricStructureStarHomeomorph_involutive S I] using
      forward ((geometricStructureStarHomeomorph S).toEquiv I) hI
  · exact forward I

/-- Restrict the full homeomorphism, not merely its finite-continuity layer. -/
def normalPartStarHomeomorph :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)) :=
  (geometricStructureStarHomeomorph S).subspace (normalPart S) (normalPart S)
    (fun I => (mem_normalPart_geometricStructureStarHomeomorph_iff S hS I).symm)

@[simp]
theorem normalPartStarHomeomorph_point (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalPartStarHomeomorph S hS).toEquiv (normalPartPoint S hS x y hx hy) =
      normalPartPoint S hS y x hy hx := by
  apply Subtype.ext
  exact geometricStructureStarHomeomorph_restrictedMatrixCoefficientKernel S hS x y hx hy

/-- Literal exchange of the two Mathlib projective factors. -/
@[simp]
theorem normalPartStarHomeomorph_projectivization (p : (ℙ ℂ H) × (ℙ ℂ H)) :
    (normalPartStarHomeomorph S hS).toEquiv (normalPartProjectivizationEquiv S hS p) =
      normalPartProjectivizationEquiv S hS p.swap :=
  normalPartStarHomeomorph_point S hS p.1.rep p.2.rep p.1.rep_nonzero p.2.rep_nonzero

/-- The restriction remains an involution, with the original normal-part type. -/
theorem normalPartStarHomeomorph_involutive :
    Function.Involutive (normalPartStarHomeomorph S hS).toEquiv := by
  intro I
  apply Subtype.ext
  exact geometricStructureStarHomeomorph_involutive S I.val

@[simp]
theorem normalPartStarHomeomorph_symm_apply (I : normalPart S) :
    (normalPartStarHomeomorph S hS).toEquiv.symm I =
      (normalPartStarHomeomorph S hS).toEquiv I := by
  have h := normalPartStarHomeomorph_involutive S hS
    ((normalPartStarHomeomorph S hS).toEquiv.symm I)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The normal-part map also has full arbitrary-set closure preservation. -/
theorem image_closure_normalPartStarHomeomorph (D : Set (normalPart S)) :
    (normalPartStarHomeomorph S hS).toEquiv ''
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D =
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        ((normalPartStarHomeomorph S hS).toEquiv '' D) :=
  (normalPartStarHomeomorph S hS).image_closure D

/-- Star interchanges the two actual maximal R-set families. -/
theorem image_normalPartSourceFiber_star (p : ℙ ℂ H) :
    (normalPartStarHomeomorph S hS).toEquiv '' normalPartSourceFiber S hS p =
      normalPartTargetFiber S hS p := by
  let e := normalPartProjectivizationEquiv S hS
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    obtain ⟨q, rfl⟩ := e.surjective J
    rw [normalPartStarHomeomorph_projectivization]
    exact (mem_normalPartTargetFiber_equiv S hS p q.swap).2
      ((mem_normalPartSourceFiber_equiv S hS p q).1 hJ)
  · intro hI
    obtain ⟨q, rfl⟩ := e.surjective I
    refine ⟨e q.swap, ?_, ?_⟩
    · exact (mem_normalPartSourceFiber_equiv S hS p q.swap).2
        ((mem_normalPartTargetFiber_equiv S hS p q).1 hI)
    · change (normalPartStarHomeomorph S hS).toEquiv
          (normalPartProjectivizationEquiv S hS q.swap) =
        normalPartProjectivizationEquiv S hS q
      rw [normalPartStarHomeomorph_projectivization, Prod.swap_swap]

/-- The reverse family exchange includes the coincident dimension-one case. -/
theorem image_normalPartTargetFiber_star (p : ℙ ℂ H) :
    (normalPartStarHomeomorph S hS).toEquiv '' normalPartTargetFiber S hS p =
      normalPartSourceFiber S hS p := by
  let e := normalPartProjectivizationEquiv S hS
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    obtain ⟨q, rfl⟩ := e.surjective J
    rw [normalPartStarHomeomorph_projectivization]
    exact (mem_normalPartSourceFiber_equiv S hS p q.swap).2
      ((mem_normalPartTargetFiber_equiv S hS p q).1 hJ)
  · intro hI
    obtain ⟨q, rfl⟩ := e.surjective I
    refine ⟨e q.swap, ?_, ?_⟩
    · exact (mem_normalPartTargetFiber_equiv S hS p q.swap).2
        ((mem_normalPartSourceFiber_equiv S hS p q).1 hI)
    · change (normalPartStarHomeomorph S hS).toEquiv
          (normalPartProjectivizationEquiv S hS q.swap) =
        normalPartProjectivizationEquiv S hS q
      rw [normalPartStarHomeomorph_projectivization, Prod.swap_swap]

end MathlibAnnex.Analysis.CStarAlgebra
