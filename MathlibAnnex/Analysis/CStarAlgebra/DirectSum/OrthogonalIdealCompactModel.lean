/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.OrthogonalIdealAssembly
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.Equiv
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.CompactOperators
import MathlibAnnex.Analysis.CStarAlgebra.CompactModelEquiv

/-!
# Compact-fiber transport of an orthogonal ideal assembly

For a given family `J` of actual closed star ideals, suppose that different
ideals annihilate one another.  Given exact star-algebra equivalences from
`Fiber J i` to the compact operators on dependent Hilbert spaces `H i`, the
existing dependent c₀ equivalence transports the orthogonal-ideal sum map to
an isometric star homomorphism `CompactOperatorC0Sum H → A`.  Its range is the
norm closure of `finiteSums J`; density is not needed for this statement.

Only after an explicit hypothesis `Dense (finiteSums J)` is supplied do we
construct an equivalence `A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H`.  The inverse is the
same transported sum map, not another chosen representation.  The final
section also accepts given exact compact representations and uses the
existing `compactOperatorStarAlgEquiv` to obtain the fiber equivalences.

This file proves neither existence of the ideal family, its orthogonality,
nor density for a particular algebra.  Exact compact models are inputs, not
consequences of an unproved elementary-ideal classification.  Their C-star
norms make the given star equivalences automatically isometric; no separate
norm hypothesis is imposed.  Indices are arbitrary and fibers are dependent;
empty indices and zero fibers are not excluded.  The target is the completed
c₀-sum of compact-operator algebras, not the finite-support algebra, the bounded
product, or all compact operators on a Hilbert direct sum.
-/



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set Topology
open scoped BigOperators CStarAlgebra ENNReal

namespace MathlibAnnex.Analysis.CStarAlgebra.ClosedStarIdeal

universe uι uA uH

variable {ι : Type uι} {A : Type uA} [NonUnitalCStarAlgebra A]
variable (J : ι → ClosedStarIdeal A) (hJ : PairwiseOrthogonal J)
variable (H : ι → Type uH)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]
variable (E : ∀ i, Fiber J i ≃⋆ₐ[ℂ]
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))

set_option backward.isDefEq.respectTransparency false in
/-- Transport the completed orthogonal-ideal sum map along the given exact
compact fiber equivalences.  No ambient density hypothesis is needed. -/
def compactC0SumHom : CompactOperatorC0Sum H →⋆ₙₐ[ℂ] A :=
  (c0SumHom J hJ).comp
    (C0DirectSum.equiv (Fiber J)
      (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
      (Equiv.refl ι) E).symm.toNonUnitalStarAlgHom

@[simp]
theorem compactC0SumHom_apply (x : CompactOperatorC0Sum H) :
    compactC0SumHom J hJ H E x =
      c0SumHom J hJ
        ((C0DirectSum.equiv (Fiber J)
          (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
          (Equiv.refl ι) E).symm x) := rfl

/-- The transported sum map preserves the completed c₀ supremum norm. -/
@[simp]
theorem norm_compactC0SumHom (x : CompactOperatorC0Sum H) :
    ‖compactC0SumHom J hJ H E x‖ = ‖x‖ := by
  rw [compactC0SumHom_apply, norm_c0SumHom, C0DirectSum.norm_equiv_symm_apply]

/-- The compact-fiber sum map is an isometry, even when its range is proper. -/
theorem isometry_compactC0SumHom : Isometry (compactC0SumHom J hJ H E) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  exact norm_compactC0SumHom J hJ H E

/-- No nonzero completed c₀-family is lost by the transported sum map. -/
theorem compactC0SumHom_injective : Function.Injective (compactC0SumHom J hJ H E) :=
  (isometry_compactC0SumHom J hJ H E).injective

/-- A single compact coordinate is sent to its actual preimage in the
corresponding ambient ideal. -/
@[simp]
theorem compactC0SumHom_single (i : ι)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) :
    compactC0SumHom J hJ H E
      (C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i T) =
      ((E i).symm T : A) := by
  have hsingle :
      C0DirectSum.equiv (Fiber J)
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
        (Equiv.refl ι) E
        (C0DirectSum.single (Fiber J) i ((E i).symm T)) =
      C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i T := by
    have h := C0DirectSum.equiv_single (Fiber J)
      (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
      (Equiv.refl ι) E i ((E i).symm T)
    change C0DirectSum.equiv (Fiber J)
      (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
      (Equiv.refl ι) E (C0DirectSum.single (Fiber J) i ((E i).symm T)) =
      C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i
        ((E i) ((E i).symm T)) at h
    exact h.trans (congrArg
      (C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i)
      ((E i).apply_symm_apply T))
  rw [← hsingle, compactC0SumHom_apply, StarAlgEquiv.symm_apply_apply, c0SumHom_single]

/-- Finite truncations are transported to finite ambient ideal sums. -/
@[simp]
theorem compactC0SumHom_truncate (s : Finset ι) (x : CompactOperatorC0Sum H) :
    compactC0SumHom J hJ H E
      (C0DirectSum.truncate
        (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) s x) =
      ∑ i ∈ s, ((E i).symm
        (C0DirectSum.eval
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i x) : A) := by
  simp only [C0DirectSum.truncate, map_sum, compactC0SumHom_single]

/-- Exact compact fiber transport does not change the ambient range of the
orthogonal-ideal sum map. -/
theorem range_compactC0SumHom :
    Set.range (compactC0SumHom J hJ H E) = Set.range (c0SumHom J hJ) := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(C0DirectSum.equiv (Fiber J)
      (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
      (Equiv.refl ι) E).symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨C0DirectSum.equiv (Fiber J)
      (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
      (Equiv.refl ι) E x, ?_⟩
    rw [compactC0SumHom_apply, StarAlgEquiv.symm_apply_apply]

/-- Without any density hypothesis, the transported compact c₀-sum has
exactly the norm-closed ambient finite-sum range. -/
theorem range_compactC0SumHom_eq_closure_finiteSums :
    Set.range (compactC0SumHom J hJ H E) = closure (finiteSums J) := by
  rw [range_compactC0SumHom, range_c0SumHom_eq_closure_finiteSums]

/-- Ambient density is the explicit additional input for surjectivity. -/
theorem compactC0SumHom_surjective (hdense : Dense (finiteSums J)) :
    Function.Surjective (compactC0SumHom J hJ H E) := by
  intro a
  obtain ⟨x, hx⟩ := c0SumHom_surjective J hJ hdense a
  refine ⟨C0DirectSum.equiv (Fiber J)
    (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
    (Equiv.refl ι) E x, ?_⟩
  simpa only [compactC0SumHom_apply, StarAlgEquiv.symm_apply_apply] using hx

set_option backward.isDefEq.respectTransparency false in
/-- The actual compact c₀-model of the ambient algebra, conditional on the
given exact fiber equivalences and on explicit norm density of finite sums.
The direction is from `A` to the completed compact c₀-sum. -/
def compactC0SumEquivOfDense (hdense : Dense (finiteSums J)) :
    A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H :=
  (c0SumEquivOfDense J hJ hdense).symm.trans
    (C0DirectSum.equiv (Fiber J)
      (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
      (Equiv.refl ι) E)

@[simp]
theorem compactC0SumEquivOfDense_apply (hdense : Dense (finiteSums J)) (a : A) :
    compactC0SumEquivOfDense J hJ H E hdense a =
      C0DirectSum.equiv (Fiber J)
        (fun i => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i))
        (Equiv.refl ι) E ((c0SumEquivOfDense J hJ hdense).symm a) := rfl

/-- The inverse of the compact c₀-model is literally the transported sum
homomorphism already constructed without density. -/
@[simp]
theorem compactC0SumEquivOfDense_symm_apply
    (hdense : Dense (finiteSums J)) (x : CompactOperatorC0Sum H) :
    (compactC0SumEquivOfDense J hJ H E hdense).symm x =
      compactC0SumHom J hJ H E x := rfl

/-- The forward coordinate formula uses exactly the specified fiber model. -/
@[simp]
theorem eval_compactC0SumEquivOfDense (hdense : Dense (finiteSums J)) (a : A) (i : ι) :
    C0DirectSum.eval
      (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i
      (compactC0SumEquivOfDense J hJ H E hdense a) =
      E i (C0DirectSum.eval (Fiber J) i ((c0SumEquivOfDense J hJ hdense).symm a)) := by
  exact C0DirectSum.eval_equiv_apply (Fiber J)
    (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
    (Equiv.refl ι) E ((c0SumEquivOfDense J hJ hdense).symm a) i

/-- On each displayed ideal, the model is its specified compact equivalence
followed by the corresponding single-coordinate embedding. -/
@[simp]
theorem compactC0SumEquivOfDense_coe (hdense : Dense (finiteSums J))
    (i : ι) (a : Fiber J i) :
    compactC0SumEquivOfDense J hJ H E hdense (a : A) =
      C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i (E i a) := by
  apply (compactC0SumEquivOfDense J hJ H E hdense).symm.injective
  calc
    (compactC0SumEquivOfDense J hJ H E hdense).symm
        (compactC0SumEquivOfDense J hJ H E hdense (a : A)) = (a : A) :=
      (compactC0SumEquivOfDense J hJ H E hdense).symm_apply_apply (a : A)
    _ = ((E i).symm (E i a) : A) :=
      congrArg (fun z : Fiber J i => (z : A)) ((E i).symm_apply_apply a).symm
    _ = compactC0SumHom J hJ H E
        (C0DirectSum.single
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i (E i a)) :=
      (compactC0SumHom_single J hJ H E i (E i a)).symm
    _ = (compactC0SumEquivOfDense J hJ H E hdense).symm
        (C0DirectSum.single
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i (E i a)) :=
      (compactC0SumEquivOfDense_symm_apply J hJ H E hdense _).symm

/-- The inverse single-coordinate formula takes values in the actual ideal
carrier before inclusion into `A`. -/
@[simp]
theorem compactC0SumEquivOfDense_symm_single (hdense : Dense (finiteSums J)) (i : ι)
    (T : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)) :
    (compactC0SumEquivOfDense J hJ H E hdense).symm
      (C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i T) =
      ((E i).symm T : A) := by
  rw [compactC0SumEquivOfDense_symm_apply, compactC0SumHom_single]

/-- The model sends finite ambient ideal sums to the corresponding finite
compact-coordinate sums. -/
@[simp]
theorem compactC0SumEquivOfDense_sum (hdense : Dense (finiteSums J))
    (s : Finset ι) (a : ∀ i, Fiber J i) :
    compactC0SumEquivOfDense J hJ H E hdense (∑ i ∈ s, (a i : A)) =
      ∑ i ∈ s, C0DirectSum.single
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i (E i (a i)) := by
  simp only [map_sum, compactC0SumEquivOfDense_coe]

/-- The conditional ambient-to-c₀ equivalence is isometric. -/
theorem isometry_compactC0SumEquivOfDense (hdense : Dense (finiteSums J)) :
    Isometry (compactC0SumEquivOfDense J hJ H E hdense) :=
  NonUnitalStarAlgHom.isometry
    (compactC0SumEquivOfDense J hJ H E hdense).toNonUnitalStarAlgHom
    (compactC0SumEquivOfDense J hJ H E hdense).injective

@[simp]
theorem norm_compactC0SumEquivOfDense (hdense : Dense (finiteSums J)) (a : A) :
    ‖compactC0SumEquivOfDense J hJ H E hdense a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map
    (compactC0SumEquivOfDense J hJ H E hdense).toNonUnitalStarAlgHom
    (compactC0SumEquivOfDense J hJ H E hdense).injective a

@[simp]
theorem norm_compactC0SumEquivOfDense_symm (hdense : Dense (finiteSums J))
    (x : CompactOperatorC0Sum H) :
    ‖(compactC0SumEquivOfDense J hJ H E hdense).symm x‖ = ‖x‖ := by
  rw [compactC0SumEquivOfDense_symm_apply, norm_compactC0SumHom]

section GivenCompactModels

variable (pi : ∀ i, NonUnitalCStarRepresentation (Fiber J i) (H i))
variable (hpi : ∀ i, IsCompactOperatorModel (pi i))

/-- A given family of exact compact representations supplies the fiber
equivalences through the existing `compactOperatorStarAlgEquiv` constructor.
Orthogonality and density remain explicit inputs. -/
def compactC0SumEquivOfModels (hdense : Dense (finiteSums J)) :
    A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H :=
  compactC0SumEquivOfDense J hJ H
    (fun i => compactOperatorStarAlgEquiv (pi i) (hpi i)) hdense

/-- In the representation-input version, each coordinate acts by the original
specified representation, not by an abstractly chosen replacement. -/
@[simp]
theorem eval_compactC0SumEquivOfModels (hdense : Dense (finiteSums J)) (a : A) (i : ι) :
    (C0DirectSum.eval
      (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i
      (compactC0SumEquivOfModels J hJ H pi hpi hdense a) : H i →L[ℂ] H i) =
      pi i (C0DirectSum.eval (Fiber J) i ((c0SumEquivOfDense J hJ hdense).symm a)) := by
  unfold compactC0SumEquivOfModels
  rw [eval_compactC0SumEquivOfDense]
  rfl

/-- The representation-input compact model also preserves the original norm. -/
@[simp]
theorem norm_compactC0SumEquivOfModels (hdense : Dense (finiteSums J)) (a : A) :
    ‖compactC0SumEquivOfModels J hJ H pi hpi hdense a‖ = ‖a‖ :=
  norm_compactC0SumEquivOfDense J hJ H
    (fun i => compactOperatorStarAlgEquiv (pi i) (hpi i)) hdense a

end GivenCompactModels

end MathlibAnnex.Analysis.CStarAlgebra.ClosedStarIdeal
