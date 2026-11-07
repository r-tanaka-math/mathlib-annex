/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarHomeomorph
import MathlibAnnex.Topology.ClosureSpace.ProductCoordinates

/-!
# Projective factors of a finite homeomorphism of normal parts

The point spaces and their closure structures are the existing normal parts.
Only their point bijections are conjugated by the actual Mathlib projective
coordinate equivalences. The existing product theorem supplies two genuine
factor equivalences, with a single global choice of orientation. Nothing in
this file asserts semilinearity or continuity on arbitrary subsets.
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

/-- Conjugation of the existing point equivalence; no new closure is put on the product. -/
def normalPartProjectiveEquiv : (ℙ ℂ H) × (ℙ ℂ H) ≃ (ℙ ℂ K) × (ℙ ℂ K) :=
  ((normalPartProjectivizationEquiv S hS).trans e.toEquiv).trans
    (normalPartProjectivizationEquiv T hT).symm

@[simp]
theorem normalPartProjectivizationEquiv_projectiveEquiv (p : (ℙ ℂ H) × (ℙ ℂ H)) :
    normalPartProjectivizationEquiv T hT (normalPartProjectiveEquiv S T hS hT e p) =
      e.toEquiv (normalPartProjectivizationEquiv S hS p) := by
  simp only [normalPartProjectiveEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

@[simp]
theorem normalPartProjectivizationEquiv_projectiveEquiv_symm
    (p : (ℙ ℂ K) × (ℙ ℂ K)) :
    normalPartProjectivizationEquiv S hS
        ((normalPartProjectiveEquiv S T hS hT e).symm p) =
      e.toEquiv.symm (normalPartProjectivizationEquiv T hT p) := by
  change normalPartProjectivizationEquiv S hS
    ((normalPartProjectivizationEquiv S hS).symm
      (e.toEquiv.symm (normalPartProjectivizationEquiv T hT p))) = _
  exact (normalPartProjectivizationEquiv S hS).apply_symm_apply _

/-- Finite continuity, not a bare point bijection, supplies the relation identification. -/
theorem sharesCoordinate_normalPartProjectiveEquiv_iff
    (p q : (ℙ ℂ H) × (ℙ ℂ H)) :
    Prod.SharesCoordinate (normalPartProjectiveEquiv S T hS hT e p)
        (normalPartProjectiveEquiv S T hS hT e q) ↔ Prod.SharesCoordinate p q := by
  calc
    Prod.SharesCoordinate (normalPartProjectiveEquiv S T hS hT e p)
        (normalPartProjectiveEquiv S T hS hT e q) ↔
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Linked
        (normalPartProjectivizationEquiv T hT (normalPartProjectiveEquiv S T hS hT e p))
        (normalPartProjectivizationEquiv T hT (normalPartProjectiveEquiv S T hS hT e q)) :=
      (linked_normalPartProjectivizationEquiv_iff T hT _ _).symm
    _ ↔ ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).Linked
        (e.toEquiv (normalPartProjectivizationEquiv S hS p))
        (e.toEquiv (normalPartProjectivizationEquiv S hS q)) := by
      rw [normalPartProjectivizationEquiv_projectiveEquiv,
        normalPartProjectivizationEquiv_projectiveEquiv]
    _ ↔ ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Linked
        (normalPartProjectivizationEquiv S hS p) (normalPartProjectivizationEquiv S hS q) :=
      e.linked_iff _ _
    _ ↔ Prod.SharesCoordinate p q := linked_normalPartProjectivizationEquiv_iff S hS p q

/-- Projective factors of a finite homeomorphism, with one global orientation.
The nonempty projective factors follow from the actual nonzero representation. -/
theorem exists_normalPart_projective_factors_or_swapped :
    (∃ f g : (ℙ ℂ H) ≃ (ℙ ℂ K), ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2)) ∨
    (∃ f g : (ℙ ℂ H) ≃ (ℙ ℂ K), ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1)) := by
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero
    (NonUnitalStarSubalgebraClass.subtype S) hS.1
  exact e.exists_prod_equivalences_or_swapped
    (normalPartProjectivizationEquiv S hS) (normalPartProjectivizationEquiv T hT)
    (linked_normalPartProjectivizationEquiv_iff S hS)
    (linked_normalPartProjectivizationEquiv_iff T hT)

/-- The inverse coordinate formula in the orientation-preserving case. -/
theorem normalPart_projective_inverse_of_factors
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    (q : (ℙ ℂ K) × (ℙ ℂ K)) :
    e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
      normalPartProjectivizationEquiv S hS (f.symm q.1, g.symm q.2) := by
  apply e.toEquiv.injective
  rw [Equiv.apply_symm_apply, he]
  simp only [Equiv.apply_symm_apply]

/-- The inverse coordinate formula includes the exchange of factors. -/
theorem normalPart_projective_inverse_of_swapped_factors
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1))
    (q : (ℙ ℂ K) × (ℙ ℂ K)) :
    e.toEquiv.symm (normalPartProjectivizationEquiv T hT q) =
      normalPartProjectivizationEquiv S hS (f.symm q.2, g.symm q.1) := by
  apply e.toEquiv.injective
  rw [Equiv.apply_symm_apply, he]
  simp only [Equiv.apply_symm_apply]

/-- Evaluation on arbitrary nonzero vectors, independent of all representative choices. -/
theorem normalPart_projective_factors_point
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (f p.1, g p.2))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    e.toEquiv (normalPartPoint S hS x y hx hy) =
      normalPartPoint T hT (f (Projectivization.mk ℂ x hx)).rep
        (g (Projectivization.mk ℂ y hy)).rep
        (f (Projectivization.mk ℂ x hx)).rep_nonzero
        (g (Projectivization.mk ℂ y hy)).rep_nonzero := by
  have h := he (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy)
  rw [normalPartProjectivizationEquiv_mk] at h
  apply Subtype.ext
  apply Subtype.ext
  exact (congrArg (fun z : normalPart T => z.val.val) h).trans
    (normalPartProjectivizationEquiv_val_val T hT
      (f (Projectivization.mk ℂ x hx), g (Projectivization.mk ℂ y hy)))

/-- The swapped version retains the literal source/target order. -/
theorem normalPart_projective_swapped_factors_point
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    e.toEquiv (normalPartPoint S hS x y hx hy) =
      normalPartPoint T hT (g (Projectivization.mk ℂ y hy)).rep
        (f (Projectivization.mk ℂ x hx)).rep
        (g (Projectivization.mk ℂ y hy)).rep_nonzero
        (f (Projectivization.mk ℂ x hx)).rep_nonzero := by
  have h := he (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy)
  rw [normalPartProjectivizationEquiv_mk] at h
  apply Subtype.ext
  apply Subtype.ext
  exact (congrArg (fun z : normalPart T => z.val.val) h).trans
    (normalPartProjectivizationEquiv_val_val T hT
      (g (Projectivization.mk ℂ y hy), f (Projectivization.mk ℂ x hx)))

/-- Postcompose with the existing full star homeomorphism to correct a swap.
Only finite continuity is claimed for the composite. -/
def normalPartFiniteHomeomorphSwap : ClosureSpace.FiniteHomeomorph
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
    ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) where
  toEquiv := e.toEquiv.trans (normalPartStarHomeomorph T hT).toEquiv
  finitelyContinuous_toFun :=
    (normalPartStarHomeomorph T hT).continuous_toFun.finitelyContinuous.comp
      e.finitelyContinuous_toFun
  finitelyContinuous_invFun := e.finitelyContinuous_invFun.comp
    (normalPartStarHomeomorph T hT).continuous_invFun.finitelyContinuous

/-- A globally swapped formula becomes a factor formula under the actual star map. -/
theorem normalPartFiniteHomeomorphSwap_projectivization
    (f g : (ℙ ℂ H) ≃ (ℙ ℂ K))
    (he : ∀ p : (ℙ ℂ H) × (ℙ ℂ H),
      e.toEquiv (normalPartProjectivizationEquiv S hS p) =
        normalPartProjectivizationEquiv T hT (g p.2, f p.1))
    (p : (ℙ ℂ H) × (ℙ ℂ H)) :
    (normalPartFiniteHomeomorphSwap S T hT e).toEquiv
        (normalPartProjectivizationEquiv S hS p) =
      normalPartProjectivizationEquiv T hT (f p.1, g p.2) := by
  change (normalPartStarHomeomorph T hT).toEquiv
    (e.toEquiv (normalPartProjectivizationEquiv S hS p)) = _
  rw [he, normalPartStarHomeomorph_projectivization]
  rfl

/-- Membership in the closure of a finite image is reflected as well as preserved.
This is a specialization to the existing normal parts, not a new closure definition. -/
theorem normalPart_finiteHomeomorph_mem_closure_image_iff
    (D : Set (normalPart S)) (hD : D.Finite) (I : normalPart S) :
    e.toEquiv I ∈
        ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure
          (e.toEquiv '' D) ↔
      I ∈ ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D := by
  constructor
  · intro h
    have hi := e.finitelyContinuous_invFun (e.toEquiv '' D) (hD.image e.toEquiv)
      ⟨e.toEquiv I, h, rfl⟩
    have hd : e.toEquiv.symm '' (e.toEquiv '' D) = D := by
      ext J
      simp
    change e.toEquiv.symm (e.toEquiv I) ∈
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
        (e.toEquiv.symm '' (e.toEquiv '' D)) at hi
    rw [e.toEquiv.symm_apply_apply, hd] at hi
    exact hi
  · intro h
    exact e.finitelyContinuous_toFun D hD ⟨I, h, rfl⟩


/-- Equality of the entire closures for a finite input set. The closure itself
need not be finite; this does not assert continuity on arbitrary input sets. -/
theorem normalPart_finiteHomeomorph_image_closure_of_finite
    (D : Set (normalPart S)) (hD : D.Finite) :
    e.toEquiv ''
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D =
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure
        (e.toEquiv '' D) := by
  ext J
  constructor
  · rintro ⟨I, hI, rfl⟩
    exact (normalPart_finiteHomeomorph_mem_closure_image_iff S T e D hD I).2 hI
  · intro hJ
    refine ⟨e.toEquiv.symm J, ?_, e.toEquiv.apply_symm_apply J⟩
    apply (normalPart_finiteHomeomorph_mem_closure_image_iff S T e D hD _).1
    simpa only [Equiv.apply_symm_apply] using hJ

end MathlibAnnex.Analysis.CStarAlgebra
