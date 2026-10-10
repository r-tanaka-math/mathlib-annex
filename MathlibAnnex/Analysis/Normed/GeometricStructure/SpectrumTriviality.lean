/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.SpectrumTransforms
public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation
public import MathlibAnnex.Topology.ClosureSpace.HullKernelTrivialComponents

/-!
# Geometric spectra with trivial components

Remark 4.8 is conditional on the component relation being equality. Example
4.9 assumes the geometric-structure closure is topologizable and uses its
previously proved T1 property. The zero space is included. No T1-to-topology
implication is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Under triviality of components the primitive spectrum is the original family of sets. -/
theorem primitiveGeometricSpectrumFamily_eq_of_related_iff_eq
    (h : ∀ I J : GeometricStructureSpace 𝕜 E,
      (geometricStructureClosure 𝕜 E).Related I J ↔ I = J) :
    primitiveGeometricSpectrumFamily 𝕜 E = geometricStructureFamily 𝕜 E :=
  ClosureSpace.HullKernel.componentKernelFamily_eq_of_forall_related_iff_eq _ _ h

/-- The original geometric-structure space and the primitive spectrum are homeomorphic. -/
noncomputable def geometricStructureHomeomorphPrimitiveSpectrumOfRelatedEq
    (h : ∀ I J : GeometricStructureSpace 𝕜 E,
      (geometricStructureClosure 𝕜 E).Related I J ↔ I = J) :
    ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E)
      (primitiveGeometricSpectrumClosure 𝕜 E) :=
  ClosureSpace.HullKernel.homeomorphComponentKernelPointOfRelatedEq _ _ h

/-- With the same exact hypothesis gamma is a homeomorphism. -/
noncomputable def geometricSpectrumHomeomorphPrimitiveSpectrumOfRelatedEq
    (h : ∀ I J : GeometricStructureSpace 𝕜 E,
      (geometricStructureClosure 𝕜 E).Related I J ↔ I = J) :
    ClosureSpace.Homeomorph (geometricSpectrumClosure 𝕜 E)
      (primitiveGeometricSpectrumClosure 𝕜 E) :=
  ClosureSpace.HullKernel.componentPointHomeomorphComponentKernelPointOfRelatedEq _ _ h

/-- This bijectivity conclusion uses trivial components in addition to the general surjectivity. -/
theorem geometricSpectrumToPrimitive_bijective_of_related_iff_eq
    (h : ∀ I J : GeometricStructureSpace 𝕜 E,
      (geometricStructureClosure 𝕜 E).Related I J ↔ I = J) :
    Function.Bijective (geometricSpectrumToPrimitive 𝕜 E) :=
  ClosureSpace.HullKernel.componentPointToComponentKernelPoint_bijective_of_forall_related_iff_eq
    _ _ h

/-- The component-set geometric spectrum is also homeomorphic to the original space. -/
noncomputable def geometricSpectrumHomeomorphGeometricStructureOfRelatedEq
    (h : ∀ I J : GeometricStructureSpace 𝕜 E,
      (geometricStructureClosure 𝕜 E).Related I J ↔ I = J) :
    ClosureSpace.Homeomorph (geometricSpectrumClosure 𝕜 E) (geometricStructureClosure 𝕜 E) :=
  (geometricSpectrumHomeomorphPrimitiveSpectrumOfRelatedEq 𝕜 E h).trans
    (geometricStructureHomeomorphPrimitiveSpectrumOfRelatedEq 𝕜 E h).symm

/-- Topologizability and the existing T1 theorem give trivial components. -/
theorem geometricStructureClosure_related_iff_eq_of_isTopologizable
    (h : (geometricStructureClosure 𝕜 E).IsTopologizable)
    (I J : GeometricStructureSpace 𝕜 E) :
    (geometricStructureClosure 𝕜 E).Related I J ↔ I = J :=
  h.related_iff_eq (isT1_geometricStructureClosure 𝕜 E) I J

/-- Example 4.9, the primitive-spectrum homeomorphism with no completeness assumption. -/
noncomputable def geometricStructureHomeomorphPrimitiveSpectrumOfIsTopologizable
    (h : (geometricStructureClosure 𝕜 E).IsTopologizable) :
    ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E)
      (primitiveGeometricSpectrumClosure 𝕜 E) :=
  geometricStructureHomeomorphPrimitiveSpectrumOfRelatedEq 𝕜 E
    (geometricStructureClosure_related_iff_eq_of_isTopologizable 𝕜 E h)

/-- Example 4.9, the component-spectrum homeomorphism, with actual inverse maps. -/
noncomputable def geometricSpectrumHomeomorphGeometricStructureOfIsTopologizable
    (h : (geometricStructureClosure 𝕜 E).IsTopologizable) :
    ClosureSpace.Homeomorph (geometricSpectrumClosure 𝕜 E) (geometricStructureClosure 𝕜 E) :=
  geometricSpectrumHomeomorphGeometricStructureOfRelatedEq 𝕜 E
    (geometricStructureClosure_related_iff_eq_of_isTopologizable 𝕜 E h)

end NormedSpace
