/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPart
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.SemilinearCoefficientRelations

/-!
# Semilinear finite homeomorphisms of the actual normal part

The spaces below are subtypes of the already defined `normalPart`, with the
subspace closure inherited from the original general GSS. Vector choices
are used only to define a function; finite coefficient relations prove its
independence of those choices and prove both inverse laws. No boundedness
is imposed on U or V. Finite continuity is not asserted to be full continuity.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]

/-- A source representative of an existing normal point. -/
def normalPartSource (I : normalPart S) : H := Classical.choose I.property

/-- A target representative of an existing normal point. -/
def normalPartTarget (I : normalPart S) : H :=
  Classical.choose (Classical.choose_spec I.property)

/-- The chosen pair is nonzero and represents the actual kernel, not a label. -/
theorem normalPart_source_target_spec (I : normalPart S) :
    normalPartSource S I ≠ 0 ∧ normalPartTarget S I ≠ 0 ∧
      {a : S | inner ℂ (normalPartTarget S I)
        ((a : H →L[ℂ] H) (normalPartSource S I)) = 0} = I.val.val :=
  Classical.choose_spec (Classical.choose_spec I.property)

/-- Membership in a normal point's underlying kernel, in chosen coordinates. -/
theorem mem_normalPart_val_iff (I : normalPart S) (a : S) :
    a ∈ I.val.val ↔ inner ℂ (normalPartTarget S I)
      ((a : H →L[ℂ] H) (normalPartSource S I)) = 0 := by
  rw [← (normalPart_source_target_spec S I).2.2]
  rfl

/-- The nonzero coefficient point in the actual normal-part subtype. -/
def normalPartPoint (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) : normalPart S :=
  ⟨restrictedMatrixCoefficientKernel S hS x y hx hy, ⟨x, y, hx, hy, rfl⟩⟩

@[simp]
theorem normalPartPoint_val_val
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalPartPoint S hS x y hx hy).val.val =
      {a : S | inner ℂ y ((a : H →L[ℂ] H) x) = 0} := rfl

/-- Every existing normal point has a nonzero coefficient representative. -/
theorem exists_normalPartPoint_eq
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S)) (I : normalPart S) :
    ∃ (x y : H) (hx : x ≠ 0) (hy : y ≠ 0), normalPartPoint S hS x y hx hy = I := by
  obtain ⟨x, y, hx, hy, hI⟩ := I.property
  exact ⟨x, y, hx, hy, Subtype.ext (Subtype.ext hI)⟩

/-- The inherited normal-part closure is the actual kernel-intersection closure. -/
theorem mem_normalPart_closure_iff (D : Set (normalPart S)) (I : normalPart S) :
    I ∈ ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D ↔
      ∀ a : S, (∀ J : normalPart S, J ∈ D → a ∈ J.val.val) → a ∈ I.val.val := by
  change (∀ a : S, (∀ J : NormedSpace.GeometricStructureSpace ℂ S,
    J ∈ (Subtype.val : normalPart S → NormedSpace.GeometricStructureSpace ℂ S) '' D →
      a ∈ J.val) → a ∈ I.val.val) ↔ _
  constructor
  · intro h a ha
    apply h a
    rintro J ⟨L, hL, rfl⟩
    exact ha L hL
  · intro h a ha
    exact h a (fun J hJ => ha J.val ⟨J, hJ, rfl⟩)

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (T : NonUnitalStarSubalgebra ℂ (K →L[ℂ] K))
variable [IsClosed (T : Set (K →L[ℂ] K))]
variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]

/-- Transport the chosen representative; the next theorem proves that the
result agrees with EVERY representative. -/
def normalPartSemilinearMap
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (U V : H ≃ₛₗ[σ] K) (I : normalPart S) : normalPart T :=
  normalPartPoint T hT (U (normalPartSource S I)) (V (normalPartTarget S I))
    (fun h => (normalPart_source_target_spec S I).1 (U.injective (h.trans (map_zero U).symm)))
    (fun h => (normalPart_source_target_spec S I).2.1 (V.injective (h.trans (map_zero V).symm)))

/-- Choice independence on the literal kernel points. -/
theorem normalPartSemilinearMap_point
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    normalPartSemilinearMap S T hT U V (normalPartPoint S hS x y hx hy) =
      normalPartPoint T hT (U x) (V y)
        (fun h => hx (U.injective (h.trans (map_zero U).symm)))
        (fun h => hy (V.injective (h.trans (map_zero V).symm))) := by
  let I := normalPartPoint S hS x y hx hy
  have hker :
      (NonUnitalCStarRepresentation.matrixCoefficient (NonUnitalStarSubalgebraClass.subtype S)
        (normalPartSource S I) (normalPartTarget S I)).ker =
      (NonUnitalCStarRepresentation.matrixCoefficient (NonUnitalStarSubalgebraClass.subtype S)
        x y).ker :=
    SetLike.coe_injective (normalPart_source_target_spec S I).2.2
  have ht := (NonUnitalCStarRepresentation.ker_matrixCoefficient_eq_semilinear_iff
    (NonUnitalStarSubalgebraClass.subtype S) (NonUnitalStarSubalgebraClass.subtype T)
    hS hT hσ U V (normalPartSource S I) (normalPartTarget S I) x y).2 hker
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun P : Submodule ℂ T => (P : Set T)) ht

/-- The chosen kernel transport has a genuine inverse, with no continuity hypothesis. -/
def normalPartSemilinearEquiv
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K) :
    normalPart S ≃ normalPart T where
  toFun := normalPartSemilinearMap S T hT U V
  invFun := normalPartSemilinearMap T S hS U.symm V.symm
  left_inv I := by
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq S hS I
    rw [normalPartSemilinearMap_point S T hS hT hσ,
      normalPartSemilinearMap_point T S hT hS hσ]
    simp only [LinearEquiv.symm_apply_apply]
  right_inv I := by
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq T hT I
    rw [normalPartSemilinearMap_point T S hT hS hσ,
      normalPartSemilinearMap_point S T hS hT hσ]
    simp only [LinearEquiv.apply_symm_apply]

/-- Full finite-set closure preservation in the forward direction. -/
theorem finitelyContinuous_normalPartSemilinearMap
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K) :
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).FinitelyContinuous
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T))
      (normalPartSemilinearMap S T hT U V) := by
  classical
  intro D hD J hJ
  obtain ⟨I, hI, rfl⟩ := hJ
  letI : Fintype D := hD.fintype
  have hi := (mem_normalPart_closure_iff S D I).1 hI
  let x : D → H := fun i => normalPartSource S i.val
  let y : D → H := fun i => normalPartTarget S i.val
  have hs : ∀ a : S,
      (∀ i : D, NonUnitalCStarRepresentation.matrixCoefficient
        (NonUnitalStarSubalgebraClass.subtype S) (x i) (y i) a = 0) →
      NonUnitalCStarRepresentation.matrixCoefficient (NonUnitalStarSubalgebraClass.subtype S)
        (normalPartSource S I) (normalPartTarget S I) a = 0 := by
    intro a ha
    apply (mem_normalPart_val_iff S I a).1
    apply hi a
    intro J hJ
    exact (mem_normalPart_val_iff S J a).2 (ha ⟨J, hJ⟩)
  have ht := (NonUnitalCStarRepresentation.forall_matrixCoefficient_eq_zero_imp_semilinear_iff
    (NonUnitalStarSubalgebraClass.subtype S) (NonUnitalStarSubalgebraClass.subtype T)
    hS hT hσ U V x y (normalPartSource S I) (normalPartTarget S I)).2 hs
  apply (mem_normalPart_closure_iff T _ _).2
  intro b hb
  apply ht b
  intro i
  exact hb (normalPartSemilinearMap S T hT U V i.val) ⟨i.val, i.property, rfl⟩

/-- Theorem 6.9, algebraic layer: the actual normal parts are finitely
homeomorphic. Both maps are justified by the finite coefficient criterion. -/
def normalPartSemilinearFiniteHomeomorph
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K) :
    ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) where
  toEquiv := normalPartSemilinearEquiv S T hS hT hσ U V
  finitelyContinuous_toFun := finitelyContinuous_normalPartSemilinearMap S T hS hT hσ U V
  finitelyContinuous_invFun :=
    finitelyContinuous_normalPartSemilinearMap T S hT hS hσ U.symm V.symm

/-- Equality of the whole closure of every finite set, including the empty set. -/
theorem image_closure_normalPartSemilinearEquiv_of_finite
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (hσ : ∀ c : ℂ, σ (star c) = star (σ c)) (U V : H ≃ₛₗ[σ] K)
    (D : Set (normalPart S)) (hD : D.Finite) :
    (normalPartSemilinearEquiv S T hS hT hσ U V) ''
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure D =
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)).closure
        ((normalPartSemilinearEquiv S T hS hT hσ U V) '' D) := by
  let e := normalPartSemilinearFiniteHomeomorph S T hS hT hσ U V
  apply Set.Subset.antisymm (e.finitelyContinuous_toFun D hD)
  intro J hJ
  have hi := e.finitelyContinuous_invFun (e.toEquiv '' D) (hD.image e.toEquiv) ⟨J, hJ, rfl⟩
  have hD' : e.toEquiv.symm '' (e.toEquiv '' D) = D := by
    ext I
    simp
  change e.toEquiv.symm J ∈
    ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).closure
      (e.toEquiv.symm '' (e.toEquiv '' D)) at hi
  rw [hD'] at hi
  exact ⟨e.toEquiv.symm J, hi, e.toEquiv.apply_symm_apply J⟩

/-- The linear specialization does not require either vector bijection to be bounded. -/
def normalPartLinearFiniteHomeomorph
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (U V : H ≃ₗ[ℂ] K) :
    ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartSemilinearFiniteHomeomorph S T hS hT (fun _ => rfl) U V

/-- The conjugate-linear specialization, still purely algebraic. -/
def normalPartConjugateLinearFiniteHomeomorph
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (hT : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype T))
    (U V : H ≃ₛₗ[starRingEnd ℂ] K) :
    ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      ((NormedSpace.geometricStructureClosure ℂ T).subspace (normalPart T)) :=
  normalPartSemilinearFiniteHomeomorph S T hS hT (fun _ => rfl) U V

end MathlibAnnex.Analysis.CStarAlgebra
