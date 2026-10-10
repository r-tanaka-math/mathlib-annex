/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactOperatorDiagonal
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactlyRepresented

/-!
# Faithful compact representations from given compact c₀ models

The existing diagonal action of `CompactOperatorC0Sum H` takes place on the
completed dependent Hilbert sum `HilbertSum H = lp H 2`, not on the bounded
product of operator fibers.  Here we compose that fixed action with a given
nonunital star homomorphism into the compact c₀-sum.  Every value of the
composite is compact.  If the given homomorphism is injective, the same
composite is faithful and isometric, and satisfies the existing predicate
`NonUnitalCStarRepresentation.IsCompactlyRepresented`.

A given equivalence `A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H` is a specialization of
this construction.  The action, coordinates, exact norm, compactness and
range statements all concern this named composite, not a representation
chosen from an existence theorem.  Its range is the compact block-diagonal
range.  There is no assertion that this range contains every compact
operator on `HilbertSum H`.

The existence of a compact c₀ model, and the existence, orthogonality or
density of any canonical ideal family producing it, are not proved here.
Indices are arbitrary, fibers are dependent, and empty indices, zero
fibers and the zero algebra are allowed.  Classical decidable equality is
used only to refer to the existing coordinate embedding API; it is not an
additional hypothesis on the index type.  No order on the source algebra,
unitality, countability, separability or nonzero-fiber hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped Classical CStarAlgebra ENNReal lp

namespace MathlibAnnex.Analysis.CStarAlgebra.CompactOperatorC0Sum

open MathlibAnnex.Analysis.InnerProductSpace

universe uι uA uH

variable {ι : Type uι} {A : Type uA} [NonUnitalCStarAlgebra A]
variable (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- The already constructed c₀ diagonal action satisfies the existing
faithful compact-representation predicate. -/
theorem isCompactlyRepresented_diagonalRepresentation :
    (diagonalRepresentation H).IsCompactlyRepresented :=
  ⟨diagonalRepresentation_injective H,
    isCompactOperator_diagonalRepresentation H⟩

/-- Compose the fixed diagonal representation with a given compact c₀-valued
nonunital star homomorphism.  The map does not depend on an injectivity proof. -/
def representationOfHom (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) :
    NonUnitalCStarRepresentation A (HilbertSum H) :=
  (diagonalRepresentation H).comp φ

/-- The action uses exactly the coordinates of the supplied homomorphism. -/
@[simp]
theorem representationOfHom_apply (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (a : A) (v : HilbertSum H) (i : ι) :
    representationOfHom H φ a v i =
      ((C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        i (φ a)) : H i →L[ℂ] H i) (v i) :=
  diagonalRepresentation_apply H (φ a) v i

/-- A coordinate subspace is acted on by the specified compact coordinate. -/
@[simp]
theorem representationOfHom_coordinateEmbedding
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) (a : A) (i : ι) (v : H i) :
    representationOfHom H φ a (coordinateEmbedding i v) =
      coordinateEmbedding i
        (((C0DirectSum.eval
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
          i (φ a)) : H i →L[ℂ] H i) v) := by
  change CompactOperatorBoundedProduct.diagonalRepresentation H (φ a).1
    (coordinateEmbedding i v) = _
  simpa only [C0DirectSum.eval_apply] using
    CompactOperatorBoundedProduct.diagonalRepresentation_coordinateEmbedding
      H (φ a).1 i v

/-- Coordinate projection intertwines the composite action with its fiber
operator, with no faithfulness assumption. -/
@[simp]
theorem coordinateProjection_representationOfHom
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (a : A) (v : HilbertSum H) (i : ι) :
    coordinateProjection i (representationOfHom H φ a v) =
      ((C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        i (φ a)) : H i →L[ℂ] H i) (coordinateProjection i v) := by
  simpa only [coordinateProjection_apply] using
    representationOfHom_apply H φ a v i

/-- Compressing the same represented operator to a coordinate recovers the
actual compact operator specified by the given c₀-valued map. -/
theorem coordinateProjection_comp_representationOfHom_comp_coordinateEmbedding
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) (a : A) (i : ι) :
    (coordinateProjection i).comp
        ((representationOfHom H φ a).comp (coordinateEmbedding i)) =
      ((C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        i (φ a)) : H i →L[ℂ] H i) := by
  apply ContinuousLinearMap.ext
  intro v
  change coordinateProjection i
    (representationOfHom H φ a (coordinateEmbedding i v)) = _
  rw [representationOfHom_coordinateEmbedding]
  simp only [coordinateProjection_apply, coordinateEmbedding_apply,
    lp.coeFn_single, Pi.single_eq_same]

/-- The source star is the Hilbert-space adjoint of the actual composite. -/
theorem adjoint_representationOfHom (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (a : A) :
    ContinuousLinearMap.adjoint (representationOfHom H φ a) =
      representationOfHom H φ (star a) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    (map_star (representationOfHom H φ) a).symm

/-- Injectivity of the given c₀-valued map makes the composite faithful. -/
theorem representationOfHom_injective (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (hφ : Function.Injective φ) : Function.Injective (representationOfHom H φ) :=
  (diagonalRepresentation_injective H).comp hφ

/-- Every represented value is compact, even before injectivity is assumed. -/
theorem isCompactOperator_representationOfHom
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) (a : A) :
    IsCompactOperator (representationOfHom H φ a) :=
  isCompactOperator_diagonalRepresentation H (φ a)

/-- The same named composite is a faithful compact-valued representation. -/
theorem isCompactlyRepresented_representationOfHom
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) (hφ : Function.Injective φ) :
    (representationOfHom H φ).IsCompactlyRepresented :=
  ⟨representationOfHom_injective H φ hφ,
    isCompactOperator_representationOfHom H φ⟩

/-- For this fixed construction, faithfulness is precisely injectivity of
the supplied map; compactness imposes no further condition. -/
theorem isCompactlyRepresented_representationOfHom_iff
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) :
    (representationOfHom H φ).IsCompactlyRepresented ↔ Function.Injective φ := by
  constructor
  · intro h a b hab
    apply h.1
    exact congrArg (diagonalRepresentation H) hab
  · exact isCompactlyRepresented_representationOfHom H φ

/-- The exact operator norm is the source norm when the input map is injective. -/
@[simp]
theorem norm_representationOfHom (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (hφ : Function.Injective φ) (a : A) :
    ‖representationOfHom H φ a‖ = ‖a‖ := by
  calc
    ‖representationOfHom H φ a‖ = ‖φ a‖ :=
      norm_diagonalRepresentation H (φ a)
    _ = ‖a‖ := NonUnitalStarAlgHom.norm_map φ hφ a

/-- The norm formula and faithfulness concern the same concrete representation. -/
theorem isometry_representationOfHom (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H)
    (hφ : Function.Injective φ) : Isometry (representationOfHom H φ) :=
  NonUnitalStarAlgHom.isometry (representationOfHom H φ)
    (representationOfHom_injective H φ hφ)

/-- Without surjectivity of the model map, only inclusion in the c₀
diagonal range is asserted. -/
theorem range_representationOfHom_le_range_diagonalRepresentation
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) :
    NonUnitalStarAlgHom.range (representationOfHom H φ) ≤
      NonUnitalStarAlgHom.range (diagonalRepresentation H) := by
  intro T hT
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range
    (representationOfHom H φ)).1 hT
  exact (NonUnitalStarAlgHom.mem_range (diagonalRepresentation H)).2 ⟨φ a, ha⟩

/-- The represented range lies in the full compact-operator algebra, but is
not asserted to equal it. -/
theorem range_representationOfHom_le_compactOperatorStarSubalgebra
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) :
    NonUnitalStarAlgHom.range (representationOfHom H φ) ≤
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H) :=
  (range_representationOfHom_le_range_diagonalRepresentation H φ).trans
    (diagonalRepresentation_range_le_compactOperatorStarSubalgebra H)

/-- The same action with codomain restricted to the actual compact operators. -/
def compactRepresentationOfHom (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) :
    A →⋆ₙₐ[ℂ] ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H) :=
  (compactDiagonalRepresentation H).comp φ

@[simp]
theorem coe_compactRepresentationOfHom_apply
    (φ : A →⋆ₙₐ[ℂ] CompactOperatorC0Sum H) (a : A) :
    ((compactRepresentationOfHom H φ a :
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (HilbertSum H)) :
        HilbertSum H →L[ℂ] HilbertSum H) = representationOfHom H φ a := rfl

/-- The actual faithful compact representation associated to a given exact
compact c₀ model.  This is a specialization, not an independent choice. -/
def representationOfEquiv (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) :
    NonUnitalCStarRepresentation A (HilbertSum H) :=
  representationOfHom H E.toNonUnitalStarAlgHom

@[simp]
theorem representationOfEquiv_apply (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (a : A) (v : HilbertSum H) (i : ι) :
    representationOfEquiv H E a v i =
      ((C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        i (E a)) : H i →L[ℂ] H i) (v i) :=
  representationOfHom_apply H E.toNonUnitalStarAlgHom a v i

@[simp]
theorem representationOfEquiv_coordinateEmbedding
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) (a : A) (i : ι) (v : H i) :
    representationOfEquiv H E a (coordinateEmbedding i v) =
      coordinateEmbedding i
        (((C0DirectSum.eval
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
          i (E a)) : H i →L[ℂ] H i) v) :=
  representationOfHom_coordinateEmbedding H E.toNonUnitalStarAlgHom a i v

@[simp]
theorem coordinateProjection_representationOfEquiv
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (a : A) (v : HilbertSum H) (i : ι) :
    coordinateProjection i (representationOfEquiv H E a v) =
      ((C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        i (E a)) : H i →L[ℂ] H i) (coordinateProjection i v) :=
  coordinateProjection_representationOfHom H E.toNonUnitalStarAlgHom a v i

/-- Faithfulness of the displayed equivalence specialization. -/
theorem representationOfEquiv_injective (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) :
    Function.Injective (representationOfEquiv H E) :=
  representationOfHom_injective H E.toNonUnitalStarAlgHom E.injective

/-- Compactness of every value of the displayed equivalence specialization. -/
theorem isCompactOperator_representationOfEquiv
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) (a : A) :
    IsCompactOperator (representationOfEquiv H E a) :=
  isCompactOperator_representationOfHom H E.toNonUnitalStarAlgHom a

/-- A given exact compact c₀ model supplies the existing compact-representation
predicate on the named diagonal composite, without an existence-only detour. -/
theorem isCompactlyRepresented_representationOfEquiv
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) :
    (representationOfEquiv H E).IsCompactlyRepresented :=
  isCompactlyRepresented_representationOfHom H E.toNonUnitalStarAlgHom E.injective

@[simp]
theorem norm_representationOfEquiv (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) (a : A) :
    ‖representationOfEquiv H E a‖ = ‖a‖ :=
  norm_representationOfHom H E.toNonUnitalStarAlgHom E.injective a

/-- The actual represented operator map, not just the abstract model, is isometric. -/
theorem isometry_representationOfEquiv (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) :
    Isometry (representationOfEquiv H E) :=
  isometry_representationOfHom H E.toNonUnitalStarAlgHom E.injective

/-- Applying the representation to the exact model preimage gives the original
c₀ diagonal operator. -/
@[simp]
theorem representationOfEquiv_symm_apply
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) (x : CompactOperatorC0Sum H) :
    representationOfEquiv H E (E.symm x) = diagonalRepresentation H x := by
  change diagonalRepresentation H (E (E.symm x)) = diagonalRepresentation H x
  rw [E.apply_symm_apply]

/-- A single compact coordinate has the expected represented operator.  This
preimage statement is restricted to diagonal single-coordinate operators. -/
theorem representationOfEquiv_symm_single
    (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) (i : ι)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) :
    representationOfEquiv H E
        (E.symm (C0DirectSum.single
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i T)) =
      (coordinateEmbedding i).comp
        ((T : H i →L[ℂ] H i).comp (coordinateProjection i)) := by
  rw [representationOfEquiv_symm_apply]
  exact diagonalRepresentation_single H i T

/-- An exact c₀ model has exactly the existing compact block-diagonal range.
This is not surjectivity onto all compact operators on the Hilbert sum. -/
theorem range_representationOfEquiv (E : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H) :
    NonUnitalStarAlgHom.range (representationOfEquiv H E) =
      NonUnitalStarAlgHom.range (diagonalRepresentation H) := by
  apply le_antisymm
  · exact range_representationOfHom_le_range_diagonalRepresentation
      H E.toNonUnitalStarAlgHom
  · intro T hT
    obtain ⟨x, hx⟩ := (NonUnitalStarAlgHom.mem_range
      (diagonalRepresentation H)).1 hT
    apply (NonUnitalStarAlgHom.mem_range (representationOfEquiv H E)).2
    refine ⟨E.symm x, ?_⟩
    rw [representationOfEquiv_symm_apply]
    exact hx

end MathlibAnnex.Analysis.CStarAlgebra.CompactOperatorC0Sum
