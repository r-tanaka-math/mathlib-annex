/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SpectralHomeomorph
import MathlibAnnex.Analysis.Normed.GeometricStructure.SpectrumMap

/-!
# Spectral homeomorphisms induced by a geometric-structure homeomorphism

Compose the independently established ordinary spectral comparisons with
MAIN's received full-closure G/P transport. These are the (primitive) spectral
homeomorphisms of Corollary 5.13. The hypothesis is the original GSS closure
homeomorphism, not a separately supplied spectral bijection. No linear map,
star isomorphism, equality of Hilbert dimensions or faithful action is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

attribute [local instance] primitiveGeometricSpectrumTopology geometricSpectrumTopology

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]
variable (e : ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A)
  (NormedSpace.geometricStructureClosure ℂ B))

/-- Corollary 5.13: ordinary homeomorphism of the actual irreducible spectra. -/
def irreducibleSpectrumHomeomorphOfGeometricStructure : IrreducibleSpectrum A ≃ₜ IrreducibleSpectrum B :=
  (irreducibleSpectrumHomeomorph A).trans
    (((NormedSpace.geometricSpectrumHomeomorph e).toTopologicalHomeomorph
      (isTopologizable_geometricSpectrumClosure A) (isTopologizable_geometricSpectrumClosure B)).trans
        (irreducibleSpectrumHomeomorph B).symm)

/-- Corollary 5.13: ordinary homeomorphism of the actual primitive ideal spectra. -/
def primitiveSpectrumHomeomorphOfGeometricStructure : PrimitiveSpectrum A ≃ₜ PrimitiveSpectrum B :=
  (primitiveSpectrumHomeomorph A).trans
    (((NormedSpace.primitiveGeometricSpectrumHomeomorph e).toTopologicalHomeomorph
      (isTopologizable_primitiveGeometricSpectrumClosure A)
      (isTopologizable_primitiveGeometricSpectrumClosure B)).trans
        (primitiveSpectrumHomeomorph B).symm)

/-- The underlying maps are the stated compositions, rather than new chosen bijections. -/
theorem irreducibleSpectrumHomeomorphOfGeometricStructure_apply (q : IrreducibleSpectrum A) :
    irreducibleSpectrumHomeomorphOfGeometricStructure e q =
      (IrreducibleSpectrum.equivGeometricSpectrum (A := B)).symm
        ((NormedSpace.geometricSpectrumHomeomorph e).toEquiv
          (IrreducibleSpectrum.equivGeometricSpectrum q)) := rfl

theorem primitiveSpectrumHomeomorphOfGeometricStructure_apply (P : PrimitiveSpectrum A) :
    primitiveSpectrumHomeomorphOfGeometricStructure e P =
      (primitiveSpectrumEquivGeometric B).symm
        ((NormedSpace.primitiveGeometricSpectrumHomeomorph e).toEquiv
          (primitiveSpectrumEquivGeometric A P)) := rfl

/-- The two actual spectral homeomorphisms commute with their kernel maps. -/
theorem kernel_irreducibleSpectrumHomeomorphOfGeometricStructure (q : IrreducibleSpectrum A) :
    IrreducibleSpectrum.kernel (irreducibleSpectrumHomeomorphOfGeometricStructure e q) =
      primitiveSpectrumHomeomorphOfGeometricStructure e (IrreducibleSpectrum.kernel q) := by
  apply (primitiveSpectrumEquivGeometric B).injective
  rw [primitiveSpectrumEquivGeometric_kernel,
    primitiveSpectrumHomeomorphOfGeometricStructure_apply,
    Equiv.apply_symm_apply, irreducibleSpectrumHomeomorphOfGeometricStructure_apply,
    Equiv.apply_symm_apply,
    NormedSpace.geometricSpectrumToPrimitive_geometricSpectrumHomeomorph,
    primitiveSpectrumEquivGeometric_kernel]

include e in
/-- Existence form of Corollary 5.13, keeping both ordinary topological conclusions. -/
theorem nonempty_spectralHomeomorphs_of_geometricStructure :
    Nonempty (IrreducibleSpectrum A ≃ₜ IrreducibleSpectrum B) ∧
      Nonempty (PrimitiveSpectrum A ≃ₜ PrimitiveSpectrum B) :=
  ⟨⟨irreducibleSpectrumHomeomorphOfGeometricStructure e⟩,
    ⟨primitiveSpectrumHomeomorphOfGeometricStructure e⟩⟩

end MathlibAnnex.Analysis.CStarAlgebra
