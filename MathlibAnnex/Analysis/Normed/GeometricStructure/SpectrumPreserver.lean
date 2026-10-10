/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.Preserver
public import MathlibAnnex.Analysis.Normed.GeometricStructure.SpectrumMap

/-!
# Geometric spectra under Birkhoff-James orthogonality preservers

The input is exactly the existing preserver interface: an equivalence of the
underlying sets and preservation and reflection of orthogonality. The original
face-defined GSS homeomorphism has already been constructed. We specialize the
concrete spectrum transport to that homeomorphism.

Unlike an arbitrary GSS homeomorphism, a preserver supplies a vector map. Only
in this setting do we identify the primitive map with the image of a subset of
the original vector space. No linearity, norm preservation, or completeness is
silently added to the orthogonality-preserver hypothesis.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v w z

namespace NormedSpace

variable (𝕜 : Type v) (𝕝 : Type z) [RCLike 𝕜] [RCLike 𝕝]
variable {E : Type u} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕝 F]
variable (T : E ≃ F)
variable (hT : ∀ x y : E, BirkhoffJamesOrthogonal 𝕝 (T x) (T y) ↔
  BirkhoffJamesOrthogonal 𝕜 x y)

/-- An orthogonality preserver induces the concrete geometric-spectrum homeomorphism. -/
def geometricSpectrumHomeomorphOfBirkhoffJames :
    ClosureSpace.Homeomorph (geometricSpectrumClosure 𝕜 E) (geometricSpectrumClosure 𝕝 F) :=
  geometricSpectrumHomeomorph (geometricStructureHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT)

/-- An orthogonality preserver induces the concrete primitive-spectrum homeomorphism. -/
def primitiveGeometricSpectrumHomeomorphOfBirkhoffJames :
    ClosureSpace.Homeomorph (primitiveGeometricSpectrumClosure 𝕜 E)
      (primitiveGeometricSpectrumClosure 𝕝 F) :=
  primitiveGeometricSpectrumHomeomorph (geometricStructureHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT)

@[simp]
theorem geometricSpectrumHomeomorphOfBirkhoffJames_toGeometricSpectrum
    (I : GeometricStructureSpace 𝕜 E) :
    (geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv
        (toGeometricSpectrum 𝕜 E I) =
      toGeometricSpectrum 𝕝 F (geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 T hT I) :=
  geometricSpectrumHomeomorph_toGeometricSpectrum _ I

@[simp]
theorem primitiveGeometricSpectrumHomeomorphOfBirkhoffJames_toPrimitiveGeometricSpectrum
    (I : GeometricStructureSpace 𝕜 E) :
    (primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv
        (toPrimitiveGeometricSpectrum 𝕜 E I) =
      toPrimitiveGeometricSpectrum 𝕝 F (geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 T hT I) :=
  primitiveGeometricSpectrumHomeomorph_toPrimitiveGeometricSpectrum _ I

/-- The inverse is given on components by the actual inverse preserver. -/
@[simp]
theorem geometricSpectrumHomeomorphOfBirkhoffJames_symm_toGeometricSpectrum
    (J : GeometricStructureSpace 𝕝 F) :
    (geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv.symm
        (toGeometricSpectrum 𝕝 F J) =
      toGeometricSpectrum 𝕜 E
        (geometricStructureEquivOfBirkhoffJames 𝕝 𝕜 T.symm
          (birkhoffJamesOrthogonal_symm_equiv 𝕜 𝕝 T hT) J) :=
  geometricSpectrumHomeomorph_symm_toGeometricSpectrum _ J

/-- The inverse primitive map is also given by the inverse preserver. -/
@[simp]
theorem primitiveGeometricSpectrumHomeomorphOfBirkhoffJames_symm_toPrimitiveGeometricSpectrum
    (J : GeometricStructureSpace 𝕝 F) :
    (primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv.symm
        (toPrimitiveGeometricSpectrum 𝕝 F J) =
      toPrimitiveGeometricSpectrum 𝕜 E
        (geometricStructureEquivOfBirkhoffJames 𝕝 𝕜 T.symm
          (birkhoffJamesOrthogonal_symm_equiv 𝕜 𝕝 T hT) J) :=
  primitiveGeometricSpectrumHomeomorph_symm_toPrimitiveGeometricSpectrum _ J

/-- Gamma commutes with the two actual maps induced by the preserver. -/
theorem geometricSpectrumToPrimitive_geometricSpectrumHomeomorphOfBirkhoffJames
    (C : GeometricSpectrum 𝕜 E) :
    geometricSpectrumToPrimitive 𝕝 F
        ((geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv C) =
      (primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv
        (geometricSpectrumToPrimitive 𝕜 E C) :=
  geometricSpectrumToPrimitive_geometricSpectrumHomeomorph _ C

/-- The geometric map sends a component family to its image under the existing GSS map. -/
theorem geometricSpectrumHomeomorphOfBirkhoffJames_val (C : GeometricSpectrum 𝕜 E) :
    ((geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv C).val =
      geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 T hT '' C.val :=
  geometricSpectrumHomeomorph_val _ C

/-- With an actual vector equivalence supplied, the primitive map is the image under it.
The proof transports the intersection, rather than treating a kernel union as a submodule. -/
theorem primitiveGeometricSpectrumHomeomorphOfBirkhoffJames_val
    (J : PrimitiveGeometricSpectrum 𝕜 E) :
    ((primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv J).val =
      T '' J.val := by
  obtain ⟨C, rfl⟩ := geometricSpectrumToPrimitive_surjective 𝕜 E J
  rw [← geometricSpectrumToPrimitive_geometricSpectrumHomeomorphOfBirkhoffJames,
    geometricSpectrumToPrimitive_val, geometricSpectrumToPrimitive_val]
  change ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕝 F)
    (((geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv C).val) =
      T '' ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕜 E) C.val
  rw [geometricSpectrumHomeomorphOfBirkhoffJames_val]
  exact (ClosureSpace.HullKernel.image_kernel T
    (geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 T hT)
    (mem_geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 T hT) C.val).symm

/-- Primitive incidence is preserved when the underlying vector map is present. -/
theorem mem_primitiveGeometricSpectrumHomeomorphOfBirkhoffJames
    (J : PrimitiveGeometricSpectrum 𝕜 E) (x : E) :
    T x ∈ ((primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv J).val ↔
      x ∈ J.val := by
  rw [primitiveGeometricSpectrumHomeomorphOfBirkhoffJames_val]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact T.injective hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The preserver-induced geometric map preserves the full closure. -/
theorem image_geometricSpectrumClosure_of_birkhoffJames (S : Set (GeometricSpectrum 𝕜 E)) :
    (geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv ''
        (geometricSpectrumClosure 𝕜 E).closure S =
      (geometricSpectrumClosure 𝕝 F).closure
        ((geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv '' S) :=
  (geometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).image_closure S

/-- The preserver-induced primitive map preserves the full closure. -/
theorem image_primitiveGeometricSpectrumClosure_of_birkhoffJames
    (S : Set (PrimitiveGeometricSpectrum 𝕜 E)) :
    (primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv ''
        (primitiveGeometricSpectrumClosure 𝕜 E).closure S =
      (primitiveGeometricSpectrumClosure 𝕝 F).closure
        ((primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).toEquiv '' S) :=
  (primitiveGeometricSpectrumHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT).image_closure S

include T hT in
/-- Injectivity of gamma is invariant under Birkhoff-James orthogonality preservers. -/
theorem geometricSpectrumToPrimitive_injective_iff_of_birkhoffJames :
    Function.Injective (geometricSpectrumToPrimitive 𝕜 E) ↔
      Function.Injective (geometricSpectrumToPrimitive 𝕝 F) :=
  geometricSpectrumToPrimitive_injective_iff_of_homeomorph
    (geometricStructureHomeomorphOfBirkhoffJames 𝕜 𝕝 T hT)

end NormedSpace
