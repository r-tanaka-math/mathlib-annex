/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.SpectrumTransforms
public import MathlibAnnex.Topology.ClosureSpace.TransformMap

/-!
# Transport of the concrete geometric spectra

A homeomorphism of geometric structure spaces acts on the concrete spectra by
conjugating the generic G/P homeomorphisms with the previously constructed
comparison homeomorphisms. In particular, the primitive map is not an image
map on subsets of the underlying normed space: the given map has domain `S(E)`,
not `E`.

The scalar fields and the universes of the normed spaces are independent.
No completeness, nontriviality, or injectivity of gamma is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v w z

namespace NormedSpace

variable {𝕜 : Type v} {𝕝 : Type z} [RCLike 𝕜] [RCLike 𝕝]
variable {E : Type u} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕝 F]
variable (e : ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E)
  (geometricStructureClosure 𝕝 F))

/-- Transport actual component sets through the generic quotient transform. -/
def geometricSpectrumHomeomorph :
    ClosureSpace.Homeomorph (geometricSpectrumClosure 𝕜 E) (geometricSpectrumClosure 𝕝 F) :=
  ((gTransformHomeomorphGeometricSpectrum 𝕜 E).symm.trans e.gHomeomorph).trans
    (gTransformHomeomorphGeometricSpectrum 𝕝 F)

/-- Transport primitive component kernels through the closed-component transform. -/
def primitiveGeometricSpectrumHomeomorph :
    ClosureSpace.Homeomorph (primitiveGeometricSpectrumClosure 𝕜 E)
      (primitiveGeometricSpectrumClosure 𝕝 F) :=
  ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).symm.trans e.pHomeomorph).trans
    (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕝 F)

/-- Compatibility of the concrete G-map with the generic G-map. -/
theorem geometricSpectrumHomeomorph_gTransform (q : (geometricStructureClosure 𝕜 E).GPoint) :
    (geometricSpectrumHomeomorph e).toEquiv
        ((gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv q) =
      (gTransformHomeomorphGeometricSpectrum 𝕝 F).toEquiv (e.gHomeomorph.toEquiv q) := by
  change (gTransformHomeomorphGeometricSpectrum 𝕝 F).toEquiv
    (e.gHomeomorph.toEquiv ((gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv.symm
      ((gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv q))) = _
  rw [Equiv.symm_apply_apply]

/-- Compatibility of the concrete P-map with the generic P-map. -/
theorem primitiveGeometricSpectrumHomeomorph_pTransform
    (p : (geometricStructureClosure 𝕜 E).PPoint) :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv
        ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv p) =
      (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕝 F).toEquiv
        (e.pHomeomorph.toEquiv p) := by
  change (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕝 F).toEquiv
    (e.pHomeomorph.toEquiv ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv.symm
      ((pTransformHomeomorphPrimitiveGeometricSpectrum 𝕜 E).toEquiv p))) = _
  rw [Equiv.symm_apply_apply]

/-- The formula `C(I) ↦ C(e(I))`, for the actual component-set spectra. -/
@[simp]
theorem geometricSpectrumHomeomorph_toGeometricSpectrum (I : GeometricStructureSpace 𝕜 E) :
    (geometricSpectrumHomeomorph e).toEquiv (toGeometricSpectrum 𝕜 E I) =
      toGeometricSpectrum 𝕝 F (e.toEquiv I) := by
  change (gTransformHomeomorphGeometricSpectrum 𝕝 F).toEquiv
    (e.gMap ((gTransformHomeomorphGeometricSpectrum 𝕜 E).toEquiv.symm
      (toGeometricSpectrum 𝕜 E I))) = _
  rw [gTransformHomeomorphGeometricSpectrum_symm_toGeometricSpectrum,
    e.gMap_toGPoint, gTransformHomeomorphGeometricSpectrum_toGPoint]

/-- The formula `J_C(I) ↦ J_C(e(I))`; this is not an image of a subset of `E`. -/
@[simp]
theorem primitiveGeometricSpectrumHomeomorph_toPrimitiveGeometricSpectrum
    (I : GeometricStructureSpace 𝕜 E) :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv (toPrimitiveGeometricSpectrum 𝕜 E I) =
      toPrimitiveGeometricSpectrum 𝕝 F (e.toEquiv I) := by
  rw [← pTransformHomeomorphPrimitiveGeometricSpectrum_toPPoint 𝕜 E I,
    primitiveGeometricSpectrumHomeomorph_pTransform]
  change (pTransformHomeomorphPrimitiveGeometricSpectrum 𝕝 F).toEquiv
    (e.pMap ((geometricStructureClosure 𝕜 E).toPPoint I)) = _
  rw [e.pMap_toPPoint, pTransformHomeomorphPrimitiveGeometricSpectrum_toPPoint]

/-- The inverse component map is given by the inverse geometric-structure map. -/
@[simp]
theorem geometricSpectrumHomeomorph_symm_toGeometricSpectrum
    (J : GeometricStructureSpace 𝕝 F) :
    (geometricSpectrumHomeomorph e).toEquiv.symm (toGeometricSpectrum 𝕝 F J) =
      toGeometricSpectrum 𝕜 E (e.toEquiv.symm J) := by
  apply (geometricSpectrumHomeomorph e).toEquiv.injective
  rw [Equiv.apply_symm_apply, geometricSpectrumHomeomorph_toGeometricSpectrum,
    Equiv.apply_symm_apply]

/-- The inverse primitive map is computed on representatives, without choosing a vector map. -/
@[simp]
theorem primitiveGeometricSpectrumHomeomorph_symm_toPrimitiveGeometricSpectrum
    (J : GeometricStructureSpace 𝕝 F) :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv.symm (toPrimitiveGeometricSpectrum 𝕝 F J) =
      toPrimitiveGeometricSpectrum 𝕜 E (e.toEquiv.symm J) := by
  apply (primitiveGeometricSpectrumHomeomorph e).toEquiv.injective
  rw [Equiv.apply_symm_apply,
    primitiveGeometricSpectrumHomeomorph_toPrimitiveGeometricSpectrum, Equiv.apply_symm_apply]

/-- The inverse equivalence equals transport by the inverse homeomorphism. -/
theorem geometricSpectrumHomeomorph_symm :
    (geometricSpectrumHomeomorph e).toEquiv.symm =
      (geometricSpectrumHomeomorph e.symm).toEquiv := by
  apply Equiv.ext
  intro C
  obtain ⟨J, rfl⟩ := toGeometricSpectrum_surjective 𝕝 F C
  simp only [geometricSpectrumHomeomorph_symm_toGeometricSpectrum,
    geometricSpectrumHomeomorph_toGeometricSpectrum]
  rfl

/-- The same inverse identity for primitive spectra. -/
theorem primitiveGeometricSpectrumHomeomorph_symm :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv.symm =
      (primitiveGeometricSpectrumHomeomorph e.symm).toEquiv := by
  apply Equiv.ext
  intro J
  obtain ⟨I, rfl⟩ := toPrimitiveGeometricSpectrum_surjective 𝕝 F J
  simp only [primitiveGeometricSpectrumHomeomorph_symm_toPrimitiveGeometricSpectrum,
    primitiveGeometricSpectrumHomeomorph_toPrimitiveGeometricSpectrum]
  rfl

/-- On component subsets the forward G-map is the actual image under `e : S(E) → S(F)`. -/
theorem geometricSpectrumHomeomorph_val (C : GeometricSpectrum 𝕜 E) :
    ((geometricSpectrumHomeomorph e).toEquiv C).val = e.toEquiv '' C.val := by
  obtain ⟨I, rfl⟩ := toGeometricSpectrum_surjective 𝕜 E C
  rw [geometricSpectrumHomeomorph_toGeometricSpectrum]
  exact (e.toFiniteHomeomorph.image_component I).symm

/-- On primitive points the correct formula is the intersection of a transported hull in `S(F)`. -/
theorem primitiveGeometricSpectrumHomeomorph_val (J : PrimitiveGeometricSpectrum 𝕜 E) :
    ((primitiveGeometricSpectrumHomeomorph e).toEquiv J).val =
      ClosureSpace.HullKernel.kernel (geometricStructureFamily 𝕝 F)
        (e.toEquiv '' {I : GeometricStructureSpace 𝕜 E | J.val ⊆ I.val}) := rfl

/-- Forward preservation of the full geometric closure, including empty selections. -/
theorem image_geometricSpectrumClosure (S : Set (GeometricSpectrum 𝕜 E)) :
    (geometricSpectrumHomeomorph e).toEquiv '' (geometricSpectrumClosure 𝕜 E).closure S =
      (geometricSpectrumClosure 𝕝 F).closure ((geometricSpectrumHomeomorph e).toEquiv '' S) :=
  (geometricSpectrumHomeomorph e).image_closure S

/-- Forward preservation of the full primitive closure. -/
theorem image_primitiveGeometricSpectrumClosure (S : Set (PrimitiveGeometricSpectrum 𝕜 E)) :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv ''
        (primitiveGeometricSpectrumClosure 𝕜 E).closure S =
      (primitiveGeometricSpectrumClosure 𝕝 F).closure
        ((primitiveGeometricSpectrumHomeomorph e).toEquiv '' S) :=
  (primitiveGeometricSpectrumHomeomorph e).image_closure S

/-- The inverse geometric map also preserves every closure. -/
theorem image_symm_geometricSpectrumClosure (S : Set (GeometricSpectrum 𝕝 F)) :
    (geometricSpectrumHomeomorph e).toEquiv.symm '' (geometricSpectrumClosure 𝕝 F).closure S =
      (geometricSpectrumClosure 𝕜 E).closure
        ((geometricSpectrumHomeomorph e).toEquiv.symm '' S) :=
  (geometricSpectrumHomeomorph e).symm.image_closure S

/-- The inverse primitive map also preserves every closure. -/
theorem image_symm_primitiveGeometricSpectrumClosure (S : Set (PrimitiveGeometricSpectrum 𝕝 F)) :
    (primitiveGeometricSpectrumHomeomorph e).toEquiv.symm ''
        (primitiveGeometricSpectrumClosure 𝕝 F).closure S =
      (primitiveGeometricSpectrumClosure 𝕜 E).closure
        ((primitiveGeometricSpectrumHomeomorph e).toEquiv.symm '' S) :=
  (primitiveGeometricSpectrumHomeomorph e).symm.image_closure S

/-- The gamma square commutes on every concrete geometric-spectrum point. -/
theorem geometricSpectrumToPrimitive_geometricSpectrumHomeomorph (C : GeometricSpectrum 𝕜 E) :
    geometricSpectrumToPrimitive 𝕝 F ((geometricSpectrumHomeomorph e).toEquiv C) =
      (primitiveGeometricSpectrumHomeomorph e).toEquiv (geometricSpectrumToPrimitive 𝕜 E C) := by
  obtain ⟨I, rfl⟩ := toGeometricSpectrum_surjective 𝕜 E C
  rw [geometricSpectrumHomeomorph_toGeometricSpectrum,
    geometricSpectrumToPrimitive_toGeometricSpectrum,
    geometricSpectrumToPrimitive_toGeometricSpectrum,
    primitiveGeometricSpectrumHomeomorph_toPrimitiveGeometricSpectrum]

/-- Function-level form of the commuting square in Corollary 4.17. -/
theorem geometricSpectrumToPrimitive_comp_geometricSpectrumHomeomorph :
    geometricSpectrumToPrimitive 𝕝 F ∘ (geometricSpectrumHomeomorph e).toEquiv =
      (primitiveGeometricSpectrumHomeomorph e).toEquiv ∘ geometricSpectrumToPrimitive 𝕜 E :=
  funext (geometricSpectrumToPrimitive_geometricSpectrumHomeomorph e)

include e in
/-- Injectivity of gamma is invariant under geometric-structure homeomorphisms.
The argument uses the two constructed bijections, not just surjectivity of gamma. -/
theorem geometricSpectrumToPrimitive_injective_iff_of_homeomorph :
    Function.Injective (geometricSpectrumToPrimitive 𝕜 E) ↔
      Function.Injective (geometricSpectrumToPrimitive 𝕝 F) := by
  constructor
  · intro hE C D hCD
    apply (geometricSpectrumHomeomorph e).toEquiv.symm.injective
    apply hE
    apply (primitiveGeometricSpectrumHomeomorph e).toEquiv.injective
    rw [← geometricSpectrumToPrimitive_geometricSpectrumHomeomorph,
      ← geometricSpectrumToPrimitive_geometricSpectrumHomeomorph,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hCD
  · intro hF C D hCD
    apply (geometricSpectrumHomeomorph e).toEquiv.injective
    apply hF
    rw [geometricSpectrumToPrimitive_geometricSpectrumHomeomorph,
      geometricSpectrumToPrimitive_geometricSpectrumHomeomorph, hCD]

end NormedSpace
