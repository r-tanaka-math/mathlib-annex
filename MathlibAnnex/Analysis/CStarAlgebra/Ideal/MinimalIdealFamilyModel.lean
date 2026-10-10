/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Ideal.OrthogonalElementary
import MathlibAnnex.Analysis.CStarAlgebra.CompactModelEquiv
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.OrthogonalIdealAssembly
import Mathlib.Tactic

/-!
# Compact models on the carriers of the canonical minimal-ideal family

The algebraic supremum of ideal submodules is identified with the literal set
`ClosedStarIdeal.finiteSums`. The proof includes zero padding outside a finite
support and absorbs scalar coefficients into the ideal coordinates.

For the canonical family of all minimal nonzero closed ideals, orthogonality
and norm density are then supplied as conclusions, not as new hypotheses.
Each ideal chooses its own generator and its own cyclic Hilbert subspace of
the given representation space. Equality with the generated ideal induces an
identity-on-ambient-elements carrier equivalence. Transport through that
carrier equivalence gives an exact compact model on the displayed ideal,
not merely on a propositionally equal generated ideal.

The final theorem exposes these same fibers, representations and equivalences
together with the actual finite-sum density. It does not use a c₀ completion or
an assembly equivalence. In the assembly module it uses only the already
specified ideal-fiber, finite-sum and orthogonality definitions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators CStarAlgebra Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uι u v

section FiniteSums

variable {ι : Type uι} {A : Type u} [NonUnitalCStarAlgebra A]

/-- The algebraic supremum of the ideal submodules and the displayed finite
ideal sums have literally the same ambient carrier. No orthogonality, order,
closedness argument, or density hypothesis is required for this equality. -/
theorem coe_closedStarIdealFiniteSumSubmodule_eq_finiteSums
    (J : ι → ClosedStarIdeal A) :
    (closedStarIdealFiniteSumSubmodule J : Set A) = ClosedStarIdeal.finiteSums J := by
  classical
  let S : Submodule ℂ A :=
    { carrier := ClosedStarIdeal.finiteSums J
      zero_mem' := by
        exact ⟨∅, fun _ => 0, by simp⟩
      add_mem' := by
        rintro a b ⟨s, x, rfl⟩ ⟨t, y, rfl⟩
        let z (i : ι) : ClosedStarIdeal.Fiber J i :=
          (if i ∈ s then x i else 0) + (if i ∈ t then y i else 0)
        refine ⟨s ∪ t, z, ?_⟩
        have hs : (∑ i ∈ s ∪ t, if i ∈ s then (x i : A) else 0) =
            ∑ i ∈ s, (x i : A) := by
          calc
            _ = ∑ i ∈ s, (if i ∈ s then (x i : A) else 0) :=
              (Finset.sum_subset Finset.subset_union_left
                (by intro i _ hi; simp only [if_neg hi])).symm
            _ = _ := Finset.sum_congr rfl (by intro i hi; simp only [if_pos hi])
        have ht : (∑ i ∈ s ∪ t, if i ∈ t then (y i : A) else 0) =
            ∑ i ∈ t, (y i : A) := by
          calc
            _ = ∑ i ∈ t, (if i ∈ t then (y i : A) else 0) :=
              (Finset.sum_subset Finset.subset_union_right
                (by intro i _ hi; simp only [if_neg hi])).symm
            _ = _ := Finset.sum_congr rfl (by intro i hi; simp only [if_pos hi])
        calc
          (∑ i ∈ s, (x i : A)) + (∑ i ∈ t, (y i : A)) =
              (∑ i ∈ s ∪ t, if i ∈ s then (x i : A) else 0) +
                (∑ i ∈ s ∪ t, if i ∈ t then (y i : A) else 0) := by rw [hs, ht]
          _ = ∑ i ∈ s ∪ t,
              ((if i ∈ s then (x i : A) else 0) +
                (if i ∈ t then (y i : A) else 0)) := by rw [Finset.sum_add_distrib]
          _ = ∑ i ∈ s ∪ t, (z i : A) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp [z, his, hit]
      smul_mem' := by
        rintro c a ⟨s, x, rfl⟩
        refine ⟨s, fun i => c • x i, ?_⟩
        simp only [Finset.smul_sum, SetLike.val_smul] }
  have hle : closedStarIdealFiniteSumSubmodule J ≤ S := by
    apply iSup_le
    intro i a ha
    change a ∈ ClosedStarIdeal.finiteSums J
    let x (j : ι) : ClosedStarIdeal.Fiber J j :=
      ⟨if j = i then a else 0, by
        by_cases hji : j = i
        · subst j
          change a ∈ (J i).toNonUnitalStarSubalgebra at ha
          simpa using ha
        · rw [if_neg hji]
          exact zero_mem _⟩
    refine ⟨{i}, x, ?_⟩
    simp [x]
  apply Set.Subset.antisymm
  · exact hle
  · rintro a ⟨s, x, ha⟩
    rw [ha]
    exact (closedStarIdealFiniteSumSubmodule J).sum_mem fun i _ =>
      (le_iSup (fun j => (J j).toNonUnitalStarSubalgebra.toSubmodule) i) (x i).property

/-- The original two-sided pairwise statement supplies the ordered
orthogonality predicate used by the assembly interface. -/
theorem pairwiseOrthogonal_minimalClosedStarIdealFamily :
    ClosedStarIdeal.PairwiseOrthogonal (minimalClosedStarIdealFamily (A := A)) := by
  letI : PartialOrder A := _root_.CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := _root_.CStarAlgebra.spectralOrderedRing A
  intro i j hij x y
  exact (pairwise_orthogonal_minimalClosedStarIdealFamily hij).1 x.property y.property

end FiniteSums

section CompactModels

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Quantitative norm density of the canonical finite-ideal-sum submodule,
transported through the literal carrier equality to the assembly's finite sums.
In particular, density is produced from the faithful compact representation. -/
theorem dense_finiteSums_minimalClosedStarIdealFamily
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    Dense (ClosedStarIdeal.finiteSums (minimalClosedStarIdealFamily (A := A))) := by
  rw [← coe_closedStarIdealFiniteSumSubmodule_eq_finiteSums]
  exact dense_minimalClosedStarIdealFiniteSumSubmodule pi hpi

namespace MinimalClosedStarIdeal

/-- A single chosen generator/vector pair for one displayed minimal ideal.
All properties are proved by `exists_generator_compactOperatorModel`; none is
an additional provider argument. Choosing the pair once fixes the fibers used
by all subsequent definitions. -/
def compactModelWitness (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    {w : A × H //
      IsMinimalStarProjection w.1 ∧ closedIdealGeneratedBy w.1 = i.1 ∧
      w.2 ≠ 0 ∧ pi w.1 w.2 = w.2 ∧
      IsCompactOperatorModel (pi.restrictClosedIdealGeneratedByCyclic w.1 w.2)} :=
  Classical.choice (show Nonempty {w : A × H //
      IsMinimalStarProjection w.1 ∧ closedIdealGeneratedBy w.1 = i.1 ∧
      w.2 ≠ 0 ∧ pi w.1 w.2 = w.2 ∧
      IsCompactOperatorModel (pi.restrictClosedIdealGeneratedByCyclic w.1 w.2)} from by
    obtain ⟨p, _, hp, hI, x, hx, hpx, hmodel⟩ :=
      i.exists_generator_compactOperatorModel pi hpi
    exact ⟨⟨(p, x), hp, hI, hx, hpx, hmodel⟩⟩)

/-- The closed cyclic subspace associated with the chosen generator/vector
pair. Different ideal indices are not identified with a fixed common fiber. -/
def compactModelSubspace (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    Submodule ℂ H :=
  (pi.restrictClosedIdealGeneratedBy (i.compactModelWitness pi hpi).val.1).cyclicSubspace
    (i.compactModelWitness pi hpi).val.2

/-- The actual dependent Hilbert carrier, with its inherited subspace norm
and complex inner product. -/
abbrev CompactModelSpace (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) : Type v :=
  i.compactModelSubspace pi hpi

/-- The displayed cyclic fiber is norm closed in the ambient Hilbert space. -/
theorem isClosed_compactModelSubspace (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    IsClosed (i.compactModelSubspace pi hpi : Set H) :=
  NonUnitalCStarRepresentation.isClosed_cyclicSubspace _ _

/-- Completeness comes from the very cyclic subspace used in the fiber's
 definition, not from an independently chosen Hilbert structure. -/
instance instCompleteSpaceCompactModelSpace (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    CompleteSpace (i.CompactModelSpace pi hpi) :=
  (i.isClosed_compactModelSubspace pi hpi).completeSpace_coe

/-- A minimal nonzero ideal has a nonzero cyclic Hilbert fiber. -/
instance instNontrivialCompactModelSpace (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    Nontrivial (i.CompactModelSpace pi hpi) := by
  let w := i.compactModelWitness pi hpi
  have hx : w.val.2 ∈ i.compactModelSubspace pi hpi := by
    have h := (pi.restrictClosedIdealGeneratedBy w.val.1).apply_mem_cyclicSubspace
      w.val.2 ⟨w.val.1, self_mem_closedIdealGeneratedBy w.val.1⟩
    change pi w.val.1 w.val.2 ∈ i.compactModelSubspace pi hpi at h
    rw [w.property.2.2.2.1] at h
    exact h
  refine ⟨⟨⟨w.val.2, hx⟩, 0, ?_⟩⟩
  intro hzero
  exact w.property.2.2.1 (congrArg Subtype.val hzero)

/-- Equality of the generated and displayed ideals induces an equivalence of
actual carriers. Its underlying ambient function is the identity. -/
def compactModelCarrierEquiv (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    i.1.toNonUnitalStarSubalgebra ≃⋆ₐ[ℂ]
      (closedIdealGeneratedBy (i.compactModelWitness pi hpi).val.1).toNonUnitalStarSubalgebra where
  toFun a := ⟨a.val, by
    have heq := congrArg (fun J : ClosedStarIdeal A => a.val ∈ J.toNonUnitalStarSubalgebra)
      (i.compactModelWitness pi hpi).property.2.1
    exact Eq.mpr heq a.property⟩
  invFun a := ⟨a.val, by
    have heq := congrArg (fun J : ClosedStarIdeal A => a.val ∈ J.toNonUnitalStarSubalgebra)
      (i.compactModelWitness pi hpi).property.2.1
    exact Eq.mp heq a.property⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl
  map_add' a b := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl
  map_star' a := Subtype.ext rfl
  map_smul' c a := Subtype.ext rfl

@[simp]
theorem coe_compactModelCarrierEquiv_apply (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (a : i.1.toNonUnitalStarSubalgebra) :
    (i.compactModelCarrierEquiv pi hpi a : A) = a := rfl

/-- The exact cyclic action transported to the displayed ideal carrier. -/
def compactModelRepresentation (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    NonUnitalCStarRepresentation i.1.toNonUnitalStarSubalgebra
      (i.CompactModelSpace pi hpi) :=
  (pi.restrictClosedIdealGeneratedByCyclic
    (i.compactModelWitness pi hpi).val.1 (i.compactModelWitness pi hpi).val.2).comp
      (i.compactModelCarrierEquiv pi hpi).toNonUnitalStarAlgHom

/-- On ambient vectors the transported action is still the original action. -/
@[simp]
theorem coe_compactModelRepresentation_apply (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (a : i.1.toNonUnitalStarSubalgebra) (z : i.CompactModelSpace pi hpi) :
    (i.compactModelRepresentation pi hpi a z : H) = pi (a : A) (z : H) := rfl

/-- Transport proves injectivity, compactness of every value, and a preimage
for every compact operator on the very same dependent fiber. -/
theorem isCompactOperatorModel_compactModelRepresentation (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    IsCompactOperatorModel (i.compactModelRepresentation pi hpi) := by
  let w := i.compactModelWitness pi hpi
  let e := i.compactModelCarrierEquiv pi hpi
  let sigma := pi.restrictClosedIdealGeneratedByCyclic w.val.1 w.val.2
  have hmodel : IsCompactOperatorModel sigma := w.property.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    change sigma (e a) = sigma (e b) at hab
    exact e.injective (hmodel.1 hab)
  · intro a
    change IsCompactOperator (sigma (e a))
    exact hmodel.2.1 (e a)
  · intro T hT
    obtain ⟨b, hb⟩ := hmodel.2.2 T hT
    refine ⟨e.symm b, ?_⟩
    change sigma (e (e.symm b)) = T
    rw [e.apply_symm_apply]
    exact hb

/-- An actual star-algebra equivalence whose domain is the displayed minimal
ideal, not just an equal generated ideal. The codomain carries the original
operator norm on the actual compact operators on its chosen cyclic fiber. -/
def compactModelEquiv (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i ≃⋆ₐ[ℂ]
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi) :=
  compactOperatorStarAlgEquiv (i.compactModelRepresentation pi hpi)
    (i.isCompactOperatorModel_compactModelRepresentation pi hpi)

/-- The equivalence and the representation agree as literal operators. -/
@[simp]
theorem coe_compactModelEquiv_apply (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    (i.compactModelEquiv pi hpi a).val = i.compactModelRepresentation pi hpi a := rfl

/-- The inverse equivalence produces an actual preimage of every compact
operator, with no representation or fiber change. -/
theorem compactModelRepresentation_compactModelEquiv_symm (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi)) :
    i.compactModelRepresentation pi hpi ((i.compactModelEquiv pi hpi).symm T) = T.val :=
  compactOperatorStarAlgEquiv_symm_apply (i.compactModelRepresentation pi hpi)
    (i.isCompactOperatorModel_compactModelRepresentation pi hpi) T

/-- The displayed ideal's inherited C-star norm agrees with the fiber's
operator norm under the chosen exact equivalence. -/
@[simp]
theorem norm_compactModelEquiv_apply (i : MinimalClosedStarIdeal A)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented)
    (a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i) :
    ‖i.compactModelEquiv pi hpi a‖ = ‖a‖ :=
  norm_compactOperatorStarAlgEquiv_apply (i.compactModelRepresentation pi hpi)
    (i.isCompactOperatorModel_compactModelRepresentation pi hpi) a

end MinimalClosedStarIdeal

/-- The canonical producer boundary: the same displayed family is pairwise
orthogonal and has norm-dense actual finite sums, and every displayed carrier
has its fixed faithful exact compact model and its fixed norm-preserving
star-algebra equivalence on the associated dependent cyclic Hilbert fiber.
No orthogonality, density, fiber model, or terminal assembly is assumed. -/
theorem minimalClosedStarIdealFamily_compactModel_spec
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsCompactlyRepresented) :
    ClosedStarIdeal.PairwiseOrthogonal (minimalClosedStarIdealFamily (A := A)) ∧
    Dense (ClosedStarIdeal.finiteSums (minimalClosedStarIdealFamily (A := A))) ∧
    ∀ i : MinimalClosedStarIdeal A,
      IsCompactOperatorModel (i.compactModelRepresentation pi hpi) ∧
      (∀ a : ClosedStarIdeal.Fiber (minimalClosedStarIdealFamily (A := A)) i,
        (i.compactModelEquiv pi hpi a).val = i.compactModelRepresentation pi hpi a ∧
        ‖i.compactModelEquiv pi hpi a‖ = ‖a‖) ∧
      (∀ T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (i.CompactModelSpace pi hpi),
        i.compactModelRepresentation pi hpi ((i.compactModelEquiv pi hpi).symm T) = T.val) := by
  refine ⟨pairwiseOrthogonal_minimalClosedStarIdealFamily,
    dense_finiteSums_minimalClosedStarIdealFamily pi hpi, ?_⟩
  intro i
  refine ⟨i.isCompactOperatorModel_compactModelRepresentation pi hpi, ?_, ?_⟩
  · intro a
    exact ⟨i.coe_compactModelEquiv_apply pi hpi a, i.norm_compactModelEquiv_apply pi hpi a⟩
  · exact i.compactModelRepresentation_compactModelEquiv_symm pi hpi

end CompactModels

end MathlibAnnex.Analysis.CStarAlgebra
