/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Topology
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralComparison
import MathlibAnnex.Topology.ClosureSpace.HullKernelMap

/-!
# Ordinary homeomorphisms in spectral reconstruction

Prim and Spec already have their independent ordinary topologies. Psi preserves
incidence in the ORIGINAL algebra, hence both hull-kernel closures. Phi preserves
closures because the representation kernels agree with J_C and both closures are
pullbacks along their respective kernel maps. Topologizability on the geometric
side is then proved. The final maps are ordinary `Homeomorph`s, not just bijections
or closure-space maps. No T0 or injectivity assumption on kappa is inserted.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]

/-- The independent primitive comparison preserves the whole hull-kernel closure. -/
def primitiveSpectrumClosureHomeomorph :
    ClosureSpace.Homeomorph (primitiveSpectrumClosure A)
      (NormedSpace.primitiveGeometricSpectrumClosure ℂ A) :=
  ClosureSpace.HullKernel.homeomorphOfMemIff
    (univ_notMem_primitiveKernelFamily A)
    (NormedSpace.univ_notMem_primitiveGeometricSpectrumFamily ℂ A)
    (Equiv.refl A) (primitiveSpectrumEquivGeometric A) (fun _ _ => Iff.rfl)

/-- Forward preservation, on EVERY selection including the empty set. -/
theorem image_primitiveSpectrumClosure (S : Set (PrimitiveSpectrum A)) :
    primitiveSpectrumEquivGeometric A '' (primitiveSpectrumClosure A).closure S =
      (NormedSpace.primitiveGeometricSpectrumClosure ℂ A).closure
        (primitiveSpectrumEquivGeometric A '' S) :=
  (primitiveSpectrumClosureHomeomorph A).image_closure S

/-- Explicit inverse preservation; the carrier identity is used in both directions. -/
theorem image_symm_primitiveGeometricSpectrumClosure
    (S : Set (NormedSpace.PrimitiveGeometricSpectrum ℂ A)) :
    (primitiveSpectrumEquivGeometric A).symm ''
        (NormedSpace.primitiveGeometricSpectrumClosure ℂ A).closure S =
      (primitiveSpectrumClosure A).closure ((primitiveSpectrumEquivGeometric A).symm '' S) :=
  (primitiveSpectrumClosureHomeomorph A).symm.image_closure S

/-- The actual bijection Phi preserves closure, via the kernel equality and
not by transporting the definition of the source topology. -/
theorem image_irreducibleSpectrumClosure (S : Set (IrreducibleSpectrum A)) :
    IrreducibleSpectrum.equivGeometricSpectrum '' (irreducibleSpectrumClosure A).closure S =
      (NormedSpace.geometricSpectrumClosure ℂ A).closure
        (IrreducibleSpectrum.equivGeometricSpectrum '' S) := by
  let e : IrreducibleSpectrum A ≃ NormedSpace.GeometricSpectrum ℂ A :=
    IrreducibleSpectrum.equivGeometricSpectrum
  rw [irreducibleSpectrumClosure_closure, NormedSpace.geometricSpectrumClosure_closure]
  ext C
  constructor
  · rintro ⟨q, hq, rfl⟩ a ha
    rw [geometricSpectrumKernel_equivGeometricSpectrum]
    apply hq a
    intro r hr
    have h := ha (e r) ⟨r, hr, rfl⟩
    exact (geometricSpectrumKernel_equivGeometricSpectrum A r) ▸ h
  · intro hC
    refine ⟨e.symm C, ?_, e.apply_symm_apply C⟩
    intro a ha
    rw [← geometricSpectrumKernel_equivGeometricSpectrum A (e.symm C)]
    change a ∈ NormedSpace.geometricSpectrumKernel ℂ A (e (e.symm C))
    rw [e.apply_symm_apply]
    apply hC a
    rintro D ⟨q, hq, rfl⟩
    rw [geometricSpectrumKernel_equivGeometricSpectrum]
    exact ha q hq

/-- The closure-space homeomorphism is proved before passing to ordinary topologies. -/
def irreducibleSpectrumClosureHomeomorph :
    ClosureSpace.Homeomorph (irreducibleSpectrumClosure A)
      (NormedSpace.geometricSpectrumClosure ℂ A) :=
  ClosureSpace.Homeomorph.ofImageClosure _ _ IrreducibleSpectrum.equivGeometricSpectrum
    (image_irreducibleSpectrumClosure A)

theorem image_symm_geometricSpectrumClosure (S : Set (NormedSpace.GeometricSpectrum ℂ A)) :
    (IrreducibleSpectrum.equivGeometricSpectrum (A := A)).symm ''
        (NormedSpace.geometricSpectrumClosure ℂ A).closure S =
      (irreducibleSpectrumClosure A).closure
        ((IrreducibleSpectrum.equivGeometricSpectrum (A := A)).symm '' S) :=
  (irreducibleSpectrumClosureHomeomorph A).symm.image_closure S

/-- Paper 5.12 for PS(A), from proved primitive-kernel primality and Psi. -/
theorem isTopologizable_primitiveGeometricSpectrumClosure :
    (NormedSpace.primitiveGeometricSpectrumClosure ℂ A).IsTopologizable :=
  (primitiveSpectrumClosureHomeomorph A).isTopologizable
    (isTopologizable_primitiveSpectrumClosure A)

/-- Paper 5.12 for GS(A). This is not deduced from any separation axiom. -/
theorem isTopologizable_geometricSpectrumClosure :
    (NormedSpace.geometricSpectrumClosure ℂ A).IsTopologizable :=
  (irreducibleSpectrumClosureHomeomorph A).isTopologizable
    (isTopologizable_irreducibleSpectrumClosure A)

/-- The ordinary topology with exactly the existing PS(A) closure. -/
def primitiveGeometricSpectrumTopology : TopologicalSpace (NormedSpace.PrimitiveGeometricSpectrum ℂ A) :=
  (NormedSpace.primitiveGeometricSpectrumClosure ℂ A).toTopologicalSpace
    (isTopologizable_primitiveGeometricSpectrumClosure A)

/-- The ordinary topology with exactly the existing GS(A) closure. -/
def geometricSpectrumTopology : TopologicalSpace (NormedSpace.GeometricSpectrum ℂ A) :=
  (NormedSpace.geometricSpectrumClosure ℂ A).toTopologicalSpace
    (isTopologizable_geometricSpectrumClosure A)

attribute [local instance] primitiveGeometricSpectrumTopology geometricSpectrumTopology

/-- Gamma retains precisely its pullback topology on the geometric side. -/
theorem geometricSpectrumTopology_eq_induced :
    geometricSpectrumTopology A = TopologicalSpace.induced
      (NormedSpace.geometricSpectrumToPrimitive ℂ A) (primitiveGeometricSpectrumTopology A) :=
  ClosureSpace.toTopologicalSpace_induced _ (isTopologizable_primitiveGeometricSpectrumClosure A) _

/-- Paper 5.11 on Prim, with ordinary forward AND inverse continuity. -/
def primitiveSpectrumHomeomorph :
    @_root_.Homeomorph (PrimitiveSpectrum A) (NormedSpace.PrimitiveGeometricSpectrum ℂ A)
      inferInstance (primitiveGeometricSpectrumTopology A) :=
  (primitiveSpectrumClosureHomeomorph A).toTopologicalHomeomorph
    (isTopologizable_primitiveSpectrumClosure A)
    (isTopologizable_primitiveGeometricSpectrumClosure A)

/-- Paper 5.11 on Spec, in its ordinary topology induced by kappa. -/
def irreducibleSpectrumHomeomorph :
    @_root_.Homeomorph (IrreducibleSpectrum A) (NormedSpace.GeometricSpectrum ℂ A)
      inferInstance (geometricSpectrumTopology A) :=
  (irreducibleSpectrumClosureHomeomorph A).toTopologicalHomeomorph
    (isTopologizable_irreducibleSpectrumClosure A) (isTopologizable_geometricSpectrumClosure A)

@[simp]
theorem primitiveSpectrumHomeomorph_toEquiv :
    (primitiveSpectrumHomeomorph A).toEquiv = primitiveSpectrumEquivGeometric A := rfl

@[simp]
theorem irreducibleSpectrumHomeomorph_toEquiv :
    (irreducibleSpectrumHomeomorph A).toEquiv = IrreducibleSpectrum.equivGeometricSpectrum := rfl

/-- The natural formula is unchanged on passing to the ordinary homeomorphism. -/
theorem irreducibleSpectrumHomeomorph_ofPureState (phi : NonUnitalPureState A) :
    irreducibleSpectrumHomeomorph A (IrreducibleSpectrum.ofPureState phi) =
      NormedSpace.toGeometricSpectrum ℂ A phi.geometricPoint := rfl

/-- The commuting square for the ordinary homeomorphisms, not just abstract bijections. -/
theorem primitiveSpectrumHomeomorph_kernel (q : IrreducibleSpectrum A) :
    primitiveSpectrumHomeomorph A (IrreducibleSpectrum.kernel q) =
      NormedSpace.geometricSpectrumToPrimitive ℂ A (irreducibleSpectrumHomeomorph A q) :=
  primitiveSpectrumEquivGeometric_kernel A q

/-- Ordinary closure on GS(A) agrees with its original, unmodified closure space. -/
theorem closure_geometricSpectrumTopology (S : Set (NormedSpace.GeometricSpectrum ℂ A)) :
    @_root_.closure _ (geometricSpectrumTopology A) S =
      (NormedSpace.geometricSpectrumClosure ℂ A).closure S :=
  ClosureSpace.closure_toTopologicalSpace _ _ S

/-- Ordinary closure on PS(A) agrees with its original, unmodified hull-kernel closure. -/
theorem closure_primitiveGeometricSpectrumTopology
    (S : Set (NormedSpace.PrimitiveGeometricSpectrum ℂ A)) :
    @_root_.closure _ (primitiveGeometricSpectrumTopology A) S =
      (NormedSpace.primitiveGeometricSpectrumClosure ℂ A).closure S :=
  ClosureSpace.closure_toTopologicalSpace _ _ S

end MathlibAnnex.Analysis.CStarAlgebra
