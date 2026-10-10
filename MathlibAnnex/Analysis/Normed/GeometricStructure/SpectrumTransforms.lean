/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Spectrum

/-!
# Identification of geometric spectra with the generic G/P transforms

This is the normed-space specialization of the proved general hull-kernel
comparison. The G-equivalence sends a quotient class to its component subset.
The P-equivalence sends a closed component to its intersection in `E`; its
inverse is the hull in `S(E)`. Both preserve full closure, and the gamma/delta
square commutes. These are not identifications of definitionally equal types.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The G-transform is homeomorphic to the actual component-set geometric spectrum. -/
noncomputable def gTransformHomeomorphGeometricSpectrum :
    ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E).gTransform
      (geometricSpectrumClosure 𝕜 E) :=
  ClosureSpace.HullKernel.gPointHomeomorphComponentPoint (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

/-- The P-transform is homeomorphic to the primitive geometric spectrum. -/
def pTransformHomeomorphPrimitiveGeometricSpectrum :
    ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E).pTransform
      (primitiveGeometricSpectrumClosure 𝕜 E) :=
  ClosureSpace.HullKernel.pPointHomeomorphComponentKernelPoint (geometricStructureFamily 𝕜 E)
    (univ_notMem_geometricStructureFamily 𝕜 E)

@[simp]
theorem gTransformHomeomorphGeometricSpectrum_toGPoint (I : GeometricStructureSpace 𝕜 E) :
    (gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv
      ((geometricStructureClosure 𝕜 E).toGPoint I) = toGeometricSpectrum 𝕜 E I := rfl

/-- The inverse G-map really recovers the quotient class from its component. -/
@[simp]
theorem gTransformHomeomorphGeometricSpectrum_symm_toGeometricSpectrum
    (I : GeometricStructureSpace 𝕜 E) :
    (gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv.symm (toGeometricSpectrum 𝕜 E I) =
      (geometricStructureClosure 𝕜 E).toGPoint I :=
  by
    rw [← gTransformHomeomorphGeometricSpectrum_toGPoint]
    exact (gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv.symm_apply_apply _

@[simp]
theorem pTransformHomeomorphPrimitiveGeometricSpectrum_toPPoint
    (I : GeometricStructureSpace 𝕜 E) :
    (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv
      ((geometricStructureClosure 𝕜 E).toPPoint I) = toPrimitiveGeometricSpectrum 𝕜 E I :=
  ClosureSpace.HullKernel.pPointEquivComponentKernelPoint_toPPoint _ _ I

/-- The forward P-map takes an intersection of original family members. -/
@[simp]
theorem pTransformHomeomorphPrimitiveGeometricSpectrum_val
    (p : (geometricStructureClosure 𝕜 E).PPoint) :
    ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv p).val =
      ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) p.val := rfl

/-- The inverse P-map is the hull in the original geometric structure space. -/
@[simp]
theorem pTransformHomeomorphPrimitiveGeometricSpectrum_symm_val
    (J : PrimitiveGeometricSpectrum 𝕜 E) :
    ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv.symm J).val =
      {I : GeometricStructureSpace 𝕜 E | J.val ⊆ I.val} := rfl

/-- Closing a component does not change its intersection in the original space. -/
theorem kernel_geometricStructureClosure_componentClosure (I : GeometricStructureSpace 𝕜 E) :
    ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E)
        ((geometricStructureClosure 𝕜 E).componentClosure I) =
      geometricSpectrumKernel 𝕜 E (toGeometricSpectrum 𝕜 E I) :=
  ClosureSpace.HullKernel.kernel_componentClosure _ _ I

/-- The component-closure/hull formula in the normed-space terminology. -/
theorem geometricStructureClosure_componentClosure_eq_hull
    (I : GeometricStructureSpace 𝕜 E) :
    (geometricStructureClosure 𝕜 E).componentClosure I =
      {I' : GeometricStructureSpace 𝕜 E |
        geometricSpectrumKernel 𝕜 E (toGeometricSpectrum 𝕜 E I) ⊆ I'.val} := rfl

/-- Distinct quotient classes can have the same intersection; the correct
criterion identifies closed components, not necessarily components themselves. -/
theorem geometricStructureClosure_componentClosure_eq_iff (I J : GeometricStructureSpace 𝕜 E) :
    (geometricStructureClosure 𝕜 E).componentClosure I =
        (geometricStructureClosure 𝕜 E).componentClosure J ↔
      (toPrimitiveGeometricSpectrum 𝕜 E I).val = (toPrimitiveGeometricSpectrum 𝕜 E J).val :=
  ClosureSpace.HullKernel.componentClosure_eq_iff_componentKernel_eq _ _ I J

/-- Lemma 4.14: intersections can be computed before or after selecting component kernels. -/
theorem kernel_primitiveGeometricSpectrumFamily (T : Set (PrimitiveGeometricSpectrum 𝕜 E)) :
    ClosureSpace.HullKernel.kernel (primitiveGeometricSpectrumFamily 𝕜 E) T =
      ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E)
        (toPrimitiveGeometricSpectrum 𝕜 E ⁻¹' T) :=
  ClosureSpace.HullKernel.kernel_componentKernelFamily _ _ T

/-- Lemma 4.15, with the closed component explicitly retained on the right. -/
theorem mem_primitiveGeometricSpectrumClosure_iff (I : GeometricStructureSpace 𝕜 E)
    (T : Set (PrimitiveGeometricSpectrum 𝕜 E)) :
    toPrimitiveGeometricSpectrum 𝕜 E I ∈ (primitiveGeometricSpectrumClosure 𝕜 E).closure T ↔
      (geometricStructureClosure 𝕜 E).componentClosure I ⊆
        (geometricStructureClosure 𝕜 E).closure (toPrimitiveGeometricSpectrum 𝕜 E ⁻¹' T) :=
  ClosureSpace.HullKernel.mem_componentKernelClosure_iff _ _ I T

/-- The commuting gamma/delta square of the two actual homeomorphisms. -/
theorem geometricSpectrumToPrimitive_gTransformHomeomorph
    (q : (geometricStructureClosure 𝕜 E).GPoint) :
    geometricSpectrumToPrimitive 𝕜 E ((gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv q) =
      (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv
        ((geometricStructureClosure 𝕜 E).delta q) :=
  ClosureSpace.HullKernel.componentPointToComponentKernelPoint_gPointEquivComponentPoint _ _ q

end NormedSpace
