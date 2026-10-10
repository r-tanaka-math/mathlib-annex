/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.ModelEquiv
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.StarAlgEquiv
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartHomeomorph
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartHilbertDimension
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralPreserver
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactOperatorC0Sum
import MathlibAnnex.Topology.ClosureSpace.ComponentSubspace

/-!
# Components and Hilbert fibers of compact-operator c₀ sums

A specified full geometric-structure homeomorphism between two actual
compact-operator c₀ sums first determines the equivalence of their independent
spectra, hence an equivalence of the index types.  The same map is then
restricted to the matched coefficient components.  The existing literal
preimage homeomorphisms identify those components with the normal parts of the
corresponding compact fibers.  Genuine Hilbert-basis cardinality, including
finite dimensions one and two, gives a complex-linear Hilbert-space isometry
equivalence on every matched fiber.

The main spectral and component statements below have explicit nonempty-index
hypotheses.  The empty/empty algebraic assembly is treated separately in the
successor rigidity module; an empty index is never called a singleton
spectrum.  No separability or countability assumption is used.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra Cardinal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uB uι uκ uH uK uI uJ

/-- Transport a specified GSS homeomorphism through two actual c₀-sum model
identifications.  Its underlying map remains the given map conjugated by the
specified model equivalences. -/
def compactDirectSumModelGeometricStructureHomeomorph
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (H : ι → Type uH) (K : κ → Type uK)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
    [∀ j, CompleteSpace (K j)]
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (F : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B)) :
    ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)) :=
  (geometricStructureHomeomorphOfStarAlgEquiv EA).symm.trans
    (F.trans (geometricStructureHomeomorphOfStarAlgEquiv EB))

@[simp]
theorem compactDirectSumModelGeometricStructureHomeomorph_apply
    {ι : Type uι} {κ : Type uκ}
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (H : ι → Type uH) (K : κ → Type uK)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
    [∀ j, CompleteSpace (K j)]
    (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
    (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
    (F : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ A)
      (NormedSpace.geometricStructureClosure ℂ B))
    (I : NormedSpace.GeometricStructureSpace ℂ (CompactOperatorC0Sum H)) :
    (compactDirectSumModelGeometricStructureHomeomorph H K EA EB F).toEquiv I =
      (geometricStructureHomeomorphOfStarAlgEquiv EB).toEquiv
        (F.toEquiv ((geometricStructureHomeomorphOfStarAlgEquiv EA).toEquiv.symm I)) := rfl

namespace CompactOperatorC0Sum

variable {ι : Type uι} {κ : Type uκ}
variable (H : ι → Type uH) (K : κ → Type uK)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]
variable [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
variable [∀ j, CompleteSpace (K j)] [∀ j, Nontrivial (K j)]

private abbrev ComponentFiberH (i : ι) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i)

private abbrev ComponentFiberK (j : κ) :=
  ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j)

private theorem nontrivial_c0_sum [Nonempty ι] :
    Nontrivial (CompactOperatorC0Sum H) := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  let a : ComponentFiberH H i := ⟨rankOne ℂ x x, isCompactOperator_rankOne x x⟩
  have ha : a ≠ 0 := by
    intro h
    apply rankOne_ne_zero (𝕜 := ℂ) hx hx
    exact congrArg Subtype.val h
  refine ⟨⟨C0DirectSum.single (fun j => ComponentFiberH H j) i a, 0, ?_⟩⟩
  intro h
  have h' := congrArg (C0DirectSum.eval (fun j => ComponentFiberH H j) i) h
  simp only [C0DirectSum.eval_single_same, map_zero] at h'
  exact ha h'

section NonemptyIndices

variable [Nonempty ι] [Nonempty κ]

local instance : Nontrivial (CompactOperatorC0Sum H) := nontrivial_c0_sum H
local instance : Nontrivial (CompactOperatorC0Sum K) := nontrivial_c0_sum K
local instance : PartialOrder (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrderedRing _
local instance : PartialOrder (CompactOperatorC0Sum K) :=
  _root_.CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (CompactOperatorC0Sum K) :=
  _root_.CStarAlgebra.spectralOrderedRing _

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

/-- The index equivalence forced by the specified full GSS homeomorphism.  It
is the actual composite through the independently defined irreducible spectra. -/
def indexEquivOfGeometricStructure
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K))) : ι ≃ κ :=
  (coordinateSpectrumEquiv H).trans
    ((irreducibleSpectrumHomeomorphOfGeometricStructure g).toEquiv.trans
      (coordinateSpectrumEquiv K).symm)

@[simp]
theorem indexEquivOfGeometricStructure_apply
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) :
    indexEquivOfGeometricStructure H K g i =
      (coordinateSpectrumEquiv K).symm
        ((irreducibleSpectrumHomeomorphOfGeometricStructure g).toEquiv
          (coordinateSpectrumEquiv H i)) := rfl

@[simp]
theorem coordinateSpectrumEquiv_indexEquivOfGeometricStructure
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) :
    coordinateSpectrumEquiv K (indexEquivOfGeometricStructure H K g i) =
      (irreducibleSpectrumHomeomorphOfGeometricStructure g).toEquiv
        (coordinateSpectrumEquiv H i) := by
  change coordinateSpectrumEquiv K
    ((coordinateSpectrumEquiv K).symm
      ((irreducibleSpectrumHomeomorphOfGeometricStructure g).toEquiv
        (coordinateSpectrumEquiv H i))) = _
  rw [Equiv.apply_symm_apply]

/-- A concrete coefficient point of the coordinate representation. -/
def coordinateCoefficientPoint (i : ι) (x : H i) (hx : x ≠ 0) :
    NormedSpace.GeometricStructureSpace ℂ (CompactOperatorC0Sum H) :=
  NonUnitalCStarRepresentation.matrixCoefficientKernel
    (coordinateRepresentation H i) (isIrreducible_coordinateRepresentation H i)
      x x hx hx

/-- The coordinate-spectrum component is the component of every nonzero
coefficient vector in the corresponding coordinate representation. -/
theorem equivGeometricSpectrum_coordinateSpectrumEquiv
    (i : ι) (x : H i) (hx : x ≠ 0) :
    IrreducibleSpectrum.equivGeometricSpectrum (coordinateSpectrumEquiv H i) =
      NormedSpace.toGeometricSpectrum ℂ (CompactOperatorC0Sum H)
        (coordinateCoefficientPoint H i x hx) := by
  change IrreducibleSpectrum.toGeometricSpectrum (coordinateSpectrumEquiv H i) = _
  simpa only [coordinateSpectrumEquiv_apply, coordinateSpectrumPoint,
    coordinateCoefficientPoint] using
    IrreducibleSpectrum.toGeometricSpectrum_ofRepresentation
      (coordinateRepresentation H i) (isIrreducible_coordinateRepresentation H i)
        x x hx hx

/-- The specified GSS homeomorphism carries the actual coefficient component
of coordinate `i` onto the actual coefficient component of its forced target
coordinate. -/
theorem image_component_coordinateCoefficientPoint
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) (x : H i) (hx : x ≠ 0)
    (y : K (indexEquivOfGeometricStructure H K g i)) (hy : y ≠ 0) :
    g.toEquiv ''
        (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).component
          (coordinateCoefficientPoint H i x hx) =
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)).component
        (coordinateCoefficientPoint K (indexEquivOfGeometricStructure H K g i) y hy) := by
  have hq := coordinateSpectrumEquiv_indexEquivOfGeometricStructure H K g i
  have hgeom := congrArg
    (IrreducibleSpectrum.equivGeometricSpectrum
      (A := CompactOperatorC0Sum K)) hq
  change IrreducibleSpectrum.equivGeometricSpectrum
      (coordinateSpectrumEquiv K (indexEquivOfGeometricStructure H K g i)) =
    IrreducibleSpectrum.equivGeometricSpectrum
      (irreducibleSpectrumHomeomorphOfGeometricStructure g
        (coordinateSpectrumEquiv H i)) at hgeom
  have hgeom' :
      (NormedSpace.geometricSpectrumHomeomorph g).toEquiv
          (NormedSpace.toGeometricSpectrum ℂ (CompactOperatorC0Sum H)
            (coordinateCoefficientPoint H i x hx)) =
        NormedSpace.toGeometricSpectrum ℂ (CompactOperatorC0Sum K)
          (coordinateCoefficientPoint K (indexEquivOfGeometricStructure H K g i) y hy) := by
    simpa only [irreducibleSpectrumHomeomorphOfGeometricStructure_apply,
      Equiv.apply_symm_apply,
      equivGeometricSpectrum_coordinateSpectrumEquiv H i x hx,
      equivGeometricSpectrum_coordinateSpectrumEquiv K
        (indexEquivOfGeometricStructure H K g i) y hy] using hgeom.symm
  have hcomponent :
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)).component
          (g.toEquiv (coordinateCoefficientPoint H i x hx)) =
        (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)).component
          (coordinateCoefficientPoint K (indexEquivOfGeometricStructure H K g i) y hy) := by
    rw [NormedSpace.geometricSpectrumHomeomorph_toGeometricSpectrum] at hgeom'
    exact congrArg Subtype.val hgeom'
  exact (g.toFiniteHomeomorph.image_component
    (coordinateCoefficientPoint H i x hx)).trans hcomponent

/-- Restriction of the specified map to the two matched coordinate components. -/
def matchedComponentHomeomorph
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) (x : H i) (hx : x ≠ 0)
    (y : K (indexEquivOfGeometricStructure H K g i)) (hy : y ≠ 0) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).subspace
        ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).component
          (coordinateCoefficientPoint H i x hx)))
      ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)).subspace
        ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)).component
          (coordinateCoefficientPoint K (indexEquivOfGeometricStructure H K g i) y hy))) :=
  g.subspace _ _ fun I => by
    have himage := image_component_coordinateCoefficientPoint H K g i x hx y hy
    constructor
    · intro hI
      rw [← himage]
      exact ⟨I, hI, rfl⟩
    · intro hI
      rw [← himage] at hI
      obtain ⟨J, hJ, hJI⟩ := hI
      exact g.toEquiv.injective hJI ▸ hJ

@[simp]
theorem matchedComponentHomeomorph_apply
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) (x : H i) (hx : x ≠ 0)
    (y : K (indexEquivOfGeometricStructure H K g i)) (hy : y ≠ 0)
    (I : (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).component
      (coordinateCoefficientPoint H i x hx)) :
    ((matchedComponentHomeomorph H K g i x hx y hy).toEquiv I).val =
      g.toEquiv I.val := rfl

/-- The coordinate representation identifies the actual compact-fiber normal
part with its coefficient component in the whole c₀ sum. -/
def coordinateNormalPartHomeomorph
    (i : ι) (x : H i) (hx : x ≠ 0) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ (ComponentFiberH H i)).subspace
        (normalPart (ComponentFiberH H i)))
      ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).subspace
        ((NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H)).component
          (coordinateCoefficientPoint H i x hx))) := by
  have h := imageNormalPartHomeomorph (coordinateRepresentation H i)
    (isIrreducible_coordinateRepresentation H i) x x hx hx
  dsimp +instances only [HomKernelQuotient.imageCStarAlgebra,
    NonUnitalStarSubalgebra.nonUnitalCStarAlgebra] at h
  rw [range_coordinateRepresentation H i] at h
  exact h

/-- Compose the literal coordinate-image identifications with the same
specified component map. -/
def matchedCoordinateNormalPartHomeomorph
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) (x : H i) (hx : x ≠ 0)
    (y : K (indexEquivOfGeometricStructure H K g i)) (hy : y ≠ 0) :
    ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ (ComponentFiberH H i)).subspace
        (normalPart (ComponentFiberH H i)))
      ((NormedSpace.geometricStructureClosure ℂ
        (ComponentFiberK K (indexEquivOfGeometricStructure H K g i))).subspace
          (normalPart (ComponentFiberK K (indexEquivOfGeometricStructure H K g i)))) :=
  (coordinateNormalPartHomeomorph H i x hx).trans
    ((matchedComponentHomeomorph H K g i x hx y hy).trans
      (coordinateNormalPartHomeomorph K
        (indexEquivOfGeometricStructure H K g i) y hy).symm)

/-- Arbitrary Hilbert bases of matched fibers have equal lifted cardinality. -/
theorem hilbertBasis_lift_mk_eq_of_matched_coordinate
    {α : Type uI} {β : Type uJ}
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) (b : HilbertBasis α ℂ (H i))
    (c : HilbertBasis β ℂ (K (indexEquivOfGeometricStructure H K g i))) :
    Cardinal.lift.{uJ} (#α) = Cardinal.lift.{uI} (#β) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  obtain ⟨y, hy⟩ := exists_ne
    (0 : K (indexEquivOfGeometricStructure H K g i))
  let f := matchedCoordinateNormalPartHomeomorph H K g i x hx y hy
  exact hilbertBasis_lift_mk_eq_of_normalPart_continuous
    (ComponentFiberH H i) (ComponentFiberK K (indexEquivOfGeometricStructure H K g i))
    (isIrreducible_compactOperatorRepresentation (H i))
    (isIrreducible_compactOperatorRepresentation
      (K (indexEquivOfGeometricStructure H K g i)))
    f.toFiniteHomeomorph f.continuous_toFun b c

/-- Every matched pair of fibers admits an actual complex-linear Hilbert-space
isometry equivalence. -/
theorem nonempty_linearIsometryEquiv_of_matched_coordinate
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) :
    Nonempty (H i ≃ₗᵢ[ℂ] K (indexEquivOfGeometricStructure H K g i)) := by
  obtain ⟨α, b, _hb⟩ := exists_hilbertBasis ℂ (H i)
  obtain ⟨β, c, _hc⟩ := exists_hilbertBasis ℂ
    (K (indexEquivOfGeometricStructure H K g i))
  obtain ⟨q⟩ := Cardinal.lift_mk_eq'.mp
    (hilbertBasis_lift_mk_eq_of_matched_coordinate H K g i b c)
  let d : HilbertBasis α ℂ (K (indexEquivOfGeometricStructure H K g i)) :=
    HilbertBasis.mk (c.orthonormal.comp q q.injective) (by
      rw [q.surjective.range_comp]
      exact c.dense_span.ge)
  exact ⟨b.repr.trans d.repr.symm⟩

/-- A fixed family of actual complex-linear fiber isometries, chosen from the
GSS-determined cardinal equalities. -/
def fiberLinearIsometryEquivOfGeometricStructure
    (g : ClosureSpace.Homeomorph
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum H))
      (NormedSpace.geometricStructureClosure ℂ (CompactOperatorC0Sum K)))
    (i : ι) : H i ≃ₗᵢ[ℂ] K (indexEquivOfGeometricStructure H K g i) :=
  Classical.choice (nonempty_linearIsometryEquiv_of_matched_coordinate H K g i)

end NonemptyIndices

end CompactOperatorC0Sum

end MathlibAnnex.Analysis.CStarAlgebra
