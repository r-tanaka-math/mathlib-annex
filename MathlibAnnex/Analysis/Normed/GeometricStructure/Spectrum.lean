/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Topology.ClosureSpace.HullKernelTransforms

/-!
# The geometric and primitive geometric spectra

The geometric spectrum consists of actual component subsets of the geometric
structure space. The primitive geometric spectrum consists of their intersections
in the original normed space. These are different types from the quotient
`GPoint` and from the closed-component `PPoint`, respectively.

The closure formulas below give the closures of Definition 4.6 and Theorem 4.7.
All intersections are intersections of sets, not submodules or ideals. Empty
intersections are `univ`. No completeness or nontriviality is required.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The geometric spectrum as a family of component subsets of `S(E)`. -/
def geometricSpectrumFamily : Set (Set (GeometricStructureSpace 𝕜 E)) :=
  (geometricStructureClosure 𝕜 E).componentFamily

/-- A point of the geometric spectrum is an actual component subset. -/
def GeometricSpectrum : Type u :=
  {C : Set (GeometricStructureSpace 𝕜 E) // C ∈ geometricSpectrumFamily 𝕜 E}

/-- The intersection `J_C` of the geometric-structure points in a component. -/
def geometricSpectrumKernel (C : GeometricSpectrum 𝕜 E) : Set E :=
  ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) C.val

/-- The primitive geometric spectrum as a family of subsets of `E`. -/
def primitiveGeometricSpectrumFamily : Set (Set E) :=
  ClosureSpace.HullKernel.componentKernelFamily (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

/-- A primitive geometric point is an intersection in `E`, not a subset of `S(E)`. -/
def PrimitiveGeometricSpectrum : Type u :=
  {J : Set E // J ∈ primitiveGeometricSpectrumFamily 𝕜 E}

/-- Send a geometric-structure point to its component. -/
def toGeometricSpectrum (I : GeometricStructureSpace 𝕜 E) : GeometricSpectrum 𝕜 E :=
  (geometricStructureClosure 𝕜 E).toComponentPoint I

/-- Send a geometric-structure point to the intersection of its component. -/
def toPrimitiveGeometricSpectrum (I : GeometricStructureSpace 𝕜 E) :
    PrimitiveGeometricSpectrum 𝕜 E :=
  ClosureSpace.HullKernel.toComponentKernelPoint (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E) I

/-- The map gamma: a component is sent to the intersection of its members.
It is surjective; injectivity is a separate condition. -/
def geometricSpectrumToPrimitive : GeometricSpectrum 𝕜 E → PrimitiveGeometricSpectrum 𝕜 E :=
  ClosureSpace.HullKernel.componentPointToComponentKernelPoint
    (geometricStructureFamily 𝕜 E) (univ_notMem_geometricStructureFamily 𝕜 E)

@[simp]
theorem geometricSpectrumToPrimitive_val (C : GeometricSpectrum 𝕜 E) :
    (geometricSpectrumToPrimitive 𝕜 E C).val = geometricSpectrumKernel 𝕜 E C := rfl

@[simp]
theorem geometricSpectrumToPrimitive_toGeometricSpectrum (I : GeometricStructureSpace 𝕜 E) :
    geometricSpectrumToPrimitive 𝕜 E (toGeometricSpectrum 𝕜 E I) =
      toPrimitiveGeometricSpectrum 𝕜 E I := rfl

theorem toGeometricSpectrum_surjective : Function.Surjective (toGeometricSpectrum 𝕜 E) :=
  (geometricStructureClosure 𝕜 E).toComponentPoint_surjective

theorem toPrimitiveGeometricSpectrum_surjective :
    Function.Surjective (toPrimitiveGeometricSpectrum 𝕜 E) :=
  ClosureSpace.HullKernel.toComponentKernelPoint_surjective _ _

theorem geometricSpectrumToPrimitive_surjective :
    Function.Surjective (geometricSpectrumToPrimitive 𝕜 E) :=
  ClosureSpace.HullKernel.componentPointToComponentKernelPoint_surjective _ _

/-- The primitive family is exactly the collection of intersections of component sets. -/
theorem primitiveGeometricSpectrumFamily_eq_range :
    primitiveGeometricSpectrumFamily 𝕜 E = Set.range (geometricSpectrumKernel 𝕜 E) := by
  apply Set.ext
  intro J
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨toGeometricSpectrum 𝕜 E I, hI⟩
  · rintro ⟨C, rfl⟩
    exact (geometricSpectrumToPrimitive 𝕜 E C).property

/-- No primitive geometric point equals the whole original space. -/
theorem univ_notMem_primitiveGeometricSpectrumFamily :
    Set.univ ∉ primitiveGeometricSpectrumFamily 𝕜 E :=
  ClosureSpace.HullKernel.univ_notMem_componentKernelFamily _ _

/-- The primitive geometric spectrum carries its own hull-kernel closure. -/
def primitiveGeometricSpectrumClosure : ClosureSpace (PrimitiveGeometricSpectrum 𝕜 E) :=
  ClosureSpace.HullKernel.componentKernelClosure (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

/-- The geometric spectrum has the closure pulled back along gamma. -/
def geometricSpectrumClosure : ClosureSpace (GeometricSpectrum 𝕜 E) :=
  (primitiveGeometricSpectrumClosure 𝕜 E).induced (geometricSpectrumToPrimitive 𝕜 E)

/-- The primitive closure formula, including the empty selection. -/
theorem primitiveGeometricSpectrumClosure_closure (T : Set (PrimitiveGeometricSpectrum 𝕜 E)) :
    (primitiveGeometricSpectrumClosure 𝕜 E).closure T =
      {J | ∀ x : E, (∀ J' : PrimitiveGeometricSpectrum 𝕜 E, J' ∈ T → x ∈ J'.val) →
        x ∈ J.val} := rfl

/-- Theorem 4.7's exact pullback formula. -/
theorem geometricSpectrumClosure_closure_preimage (S : Set (GeometricSpectrum 𝕜 E)) :
    (geometricSpectrumClosure 𝕜 E).closure S =
      geometricSpectrumToPrimitive 𝕜 E ⁻¹'
        (primitiveGeometricSpectrumClosure 𝕜 E).closure
          (geometricSpectrumToPrimitive 𝕜 E '' S) := rfl

/-- The geometric closure formula stated directly in terms of `J_C`. -/
theorem geometricSpectrumClosure_closure (S : Set (GeometricSpectrum 𝕜 E)) :
    (geometricSpectrumClosure 𝕜 E).closure S =
      {C | ∀ x : E, (∀ D : GeometricSpectrum 𝕜 E, D ∈ S →
        x ∈ geometricSpectrumKernel 𝕜 E D) → x ∈ geometricSpectrumKernel 𝕜 E C} := by
  apply Set.ext
  intro C
  change (∀ x : E, (∀ J : PrimitiveGeometricSpectrum 𝕜 E,
    J ∈ geometricSpectrumToPrimitive 𝕜 E '' S → x ∈ J.val) →
      x ∈ geometricSpectrumKernel 𝕜 E C) ↔ _
  constructor
  · intro h x hx
    apply h x
    rintro J ⟨D, hD, rfl⟩
    exact hx D hD
  · intro h x hx
    exact h x (fun D hD => hx (geometricSpectrumToPrimitive 𝕜 E D) ⟨D, hD, rfl⟩)

/-- Gamma is continuous between the two explicit closure spaces. -/
theorem continuous_geometricSpectrumToPrimitive :
    (geometricSpectrumClosure 𝕜 E).Continuous (primitiveGeometricSpectrumClosure 𝕜 E)
      (geometricSpectrumToPrimitive 𝕜 E) := ClosureSpace.continuous_induced _ _

/-- Surjectivity also gives the exact image-of-closure formula. -/
theorem image_geometricSpectrumToPrimitive_closure (S : Set (GeometricSpectrum 𝕜 E)) :
    geometricSpectrumToPrimitive 𝕜 E '' (geometricSpectrumClosure 𝕜 E).closure S =
      (primitiveGeometricSpectrumClosure 𝕜 E).closure (geometricSpectrumToPrimitive 𝕜 E '' S) :=
  ClosureSpace.image_induced_closure _ _ (geometricSpectrumToPrimitive_surjective 𝕜 E) S

/-- The primitive spectrum is T0 by its actual hull-kernel realization. -/
theorem isT0_primitiveGeometricSpectrumClosure : (primitiveGeometricSpectrumClosure 𝕜 E).IsT0 :=
  ClosureSpace.HullKernel.isT0_space (primitiveGeometricSpectrumFamily 𝕜 E)
    (univ_notMem_primitiveGeometricSpectrumFamily 𝕜 E)

/-- The geometric spectrum is T0 exactly when gamma is injective, not just surjective. -/
theorem isT0_geometricSpectrumClosure_iff :
    (geometricSpectrumClosure 𝕜 E).IsT0 ↔ Function.Injective (geometricSpectrumToPrimitive 𝕜 E) :=
  ClosureSpace.isT0_induced_iff _ (isT0_primitiveGeometricSpectrumClosure 𝕜 E) _

/-- In the zero-space case, the component family remains empty. -/
theorem geometricSpectrumFamily_eq_empty_of_subsingleton [Subsingleton E] :
    geometricSpectrumFamily 𝕜 E = ∅ := by
  letI := isEmpty_geometricStructureSpace_of_subsingleton 𝕜 E
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro C ⟨I, _⟩
  exact (Set.eq_empty_iff_forall_notMem.mp
    (geometricStructureFamily_eq_empty_of_subsingleton 𝕜 E)) I.val I.property

/-- Empty geometric-structure spaces yield no primitive geometric point. -/
theorem primitiveGeometricSpectrumFamily_eq_empty_of_subsingleton [Subsingleton E] :
    primitiveGeometricSpectrumFamily 𝕜 E = ∅ := by
  letI := isEmpty_geometricStructureSpace_of_subsingleton 𝕜 E
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro J ⟨I, _⟩
  exact (Set.eq_empty_iff_forall_notMem.mp
    (geometricStructureFamily_eq_empty_of_subsingleton 𝕜 E)) I.val I.property

/-- The type-level zero-space statement for the geometric spectrum. -/
theorem isEmpty_geometricSpectrum_of_subsingleton [Subsingleton E] :
    IsEmpty (GeometricSpectrum 𝕜 E) := by
  refine ⟨fun C => ?_⟩
  exact (Set.eq_empty_iff_forall_notMem.mp
    (geometricSpectrumFamily_eq_empty_of_subsingleton 𝕜 E)) C.val C.property

/-- The type-level zero-space statement for the primitive geometric spectrum. -/
theorem isEmpty_primitiveGeometricSpectrum_of_subsingleton [Subsingleton E] :
    IsEmpty (PrimitiveGeometricSpectrum 𝕜 E) := by
  refine ⟨fun J => ?_⟩
  exact (Set.eq_empty_iff_forall_notMem.mp
    (primitiveGeometricSpectrumFamily_eq_empty_of_subsingleton 𝕜 E)) J.val J.property

end NormedSpace
