/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientPair
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CoefficientFamily
import MathlibAnnex.Analysis.Normed.GeometricStructure.Spectrum

/-!
# Actual components and irreducible representations

Each point in a finite chain is given its own actual extreme-functional
representative and original-algebra cyclic coefficient model. The existing
`Relation.EqvGen` induction transports unitary equivalence along that chain.
Nothing is proved by identifying representation kernels with functional kernels.

The full component, not just a subset of it, is the coefficient-kernel family.
Only after this equality is established is its intersection transported to the
received geometric spectrum and the actual map gamma.
-/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped CStarAlgebra ComplexOrder

namespace MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation

universe u v w
variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private def componentContinuousMap (pi : NonUnitalCStarRepresentation A H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := pi, map_add' := map_add pi, map_smul' := map_smul pi }
    1 (fun a => by
      change ‖pi a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le pi a)

/-- The reverse direction of the component/representation bridge. Intermediate
points in the received finite-chain relation are realized, not postulated to
have a representation attached to their labels. -/
theorem unitaryEquivalent_of_related_matrixCoefficientKernel
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hrel : (NormedSpace.geometricStructureClosure ℂ A).Related
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel sigma hsigma z w hz hw)) :
    pi.UnitaryEquivalent sigma := by
  classical
  let c := NormedSpace.geometricStructureClosure ℂ A
  choose rho hext hker using fun I : NormedSpace.GeometricStructureSpace ℂ A =>
    (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall I.val).1 I.property
  have hn (I : NormedSpace.GeometricStructureSpace ℂ A) : ‖rho I‖ = 1 :=
    norm_eq_one_of_mem_extremePoints_dual_closedBall (hext I)
  have h0 (I : NormedSpace.GeometricStructureSpace ℂ A) : rho I ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hn I]; exact one_ne_zero)
  let r (I : NormedSpace.GeometricStructureSpace ℂ A) :=
    NonUnitalFunctional.cyclicRepresentation (rho I) (h0 I)
  let p (I : NormedSpace.GeometricStructureSpace ℂ A) :=
    NonUnitalFunctional.cyclicSourceVector (rho I) (h0 I)
  let q (I : NormedSpace.GeometricStructureSpace ℂ A) :=
    NonUnitalFunctional.cyclicTargetVector (rho I) (h0 I)
  have hirr (I : NormedSpace.GeometricStructureSpace ℂ A) : (r I).IsIrreducible :=
    NonUnitalFunctional.isIrreducible_cyclicRepresentation (rho I) (h0 I) (hext I)
  have hp (I : NormedSpace.GeometricStructureSpace ℂ A) : p I ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [NonUnitalFunctional.norm_cyclicSourceVector]; exact one_ne_zero)
  have hq (I : NormedSpace.GeometricStructureSpace ℂ A) : q I ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [NonUnitalFunctional.norm_cyclicTargetVector]; exact one_ne_zero)
  have hpoint (I : NormedSpace.GeometricStructureSpace ℂ A) :
      matrixCoefficientKernel (r I) (hirr I) (p I) (q I) (hp I) (hq I) = I := by
    apply Subtype.ext
    change ((matrixCoefficient (r I) (p I) (q I)).ker : Set A) = I.val
    rw [NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one _ _ (hn I)]
    exact hker I
  have hchain {I J : NormedSpace.GeometricStructureSpace ℂ A} (h : c.Related I J) :
      (r I).UnitaryEquivalent (r J) := by
    change Relation.EqvGen c.Linked I J at h
    induction h with
    | rel I J hIJ =>
        apply unitaryEquivalent_of_linked_matrixCoefficientKernel (r I) (r J) (hirr I) (hirr J)
          (p I) (q I) (p J) (q J) (hp I) (hq I) (hp J) (hq J)
        rw [hpoint I, hpoint J]
        exact hIJ
    | refl I => exact unitaryEquivalent_refl (r I)
    | symm I J _ ih => exact ih.symm
    | trans I J L _ _ ih1 ih2 => exact ih1.trans ih2
  let P := matrixCoefficientKernel pi hpi x y hx hy
  let Q := matrixCoefficientKernel sigma hsigma z w hz hw
  have hstart : pi.UnitaryEquivalent (r P) :=
    unitaryEquivalent_of_linked_matrixCoefficientKernel pi (r P) hpi (hirr P)
      x y (p P) (q P) hx hy (hp P) (hq P) (Or.inl (hpoint P).symm)
  have hend : sigma.UnitaryEquivalent (r Q) :=
    unitaryEquivalent_of_linked_matrixCoefficientKernel sigma (r Q) hsigma (hirr Q)
      z w (p Q) (q Q) hz hw (hp Q) (hq Q) (Or.inl (hpoint Q).symm)
  exact hstart.trans ((hchain hrel).trans hend.symm)

/-- Same component is exactly unitary equivalence, for arbitrary nonzero
coefficient vectors in arbitrary nonzero irreducible representations. -/
theorem related_matrixCoefficientKernel_iff_unitaryEquivalent
    (pi : NonUnitalCStarRepresentation A H) (sigma : NonUnitalCStarRepresentation A K)
    (hpi : pi.IsIrreducible) (hsigma : sigma.IsIrreducible)
    (x y : H) (z w : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).Related
      (matrixCoefficientKernel pi hpi x y hx hy) (matrixCoefficientKernel sigma hsigma z w hz hw) ↔
        pi.UnitaryEquivalent sigma :=
  ⟨unitaryEquivalent_of_related_matrixCoefficientKernel pi sigma hpi hsigma x y z w hx hy hz hw,
    fun h => related_matrixCoefficientKernel_of_unitaryEquivalent
      pi sigma hpi hsigma h x y z w hx hy hz hw⟩

/-- The entire component equals the coefficient-kernel family. The reverse
inclusion realizes an arbitrary component point and uses the proved converse
of the finite-chain bridge before transporting its actual coefficient vectors. -/
theorem component_matrixCoefficientKernel_eq_family
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricStructureClosure ℂ A).component
      (matrixCoefficientKernel pi hpi x y hx hy) = matrixCoefficientKernelFamily pi hpi := by
  apply Set.Subset.antisymm
  · intro I hI
    obtain ⟨rho, hext, hker⟩ :=
      (mem_geometricStructureFamily_iff_exists_mem_extremePoints_dual_closedBall I.val).1 I.property
    have hn : ‖rho‖ = 1 := norm_eq_one_of_mem_extremePoints_dual_closedBall hext
    have h0 : rho ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
    let r := NonUnitalFunctional.cyclicRepresentation rho h0
    let p := NonUnitalFunctional.cyclicSourceVector rho h0
    let q := NonUnitalFunctional.cyclicTargetVector rho h0
    have hirr : r.IsIrreducible := NonUnitalFunctional.isIrreducible_cyclicRepresentation rho h0 hext
    have hp : p ≠ 0 := norm_ne_zero_iff.mp (by rw [NonUnitalFunctional.norm_cyclicSourceVector]; exact one_ne_zero)
    have hq : q ≠ 0 := norm_ne_zero_iff.mp (by rw [NonUnitalFunctional.norm_cyclicTargetVector]; exact one_ne_zero)
    have hpoint : matrixCoefficientKernel r hirr p q hp hq = I := by
      apply Subtype.ext
      change ((matrixCoefficient r p q).ker : Set A) = I.val
      rw [NonUnitalFunctional.matrixCoefficient_cyclicRepresentation_of_norm_eq_one _ _ hn]
      exact hker
    have hrel : (NormedSpace.geometricStructureClosure ℂ A).Related
        (matrixCoefficientKernel r hirr p q hp hq) (matrixCoefficientKernel pi hpi x y hx hy) := by
      rw [hpoint]
      exact (NormedSpace.geometricStructureClosure ℂ A).related_symm hI
    obtain ⟨U, hU⟩ :=
      unitaryEquivalent_of_related_matrixCoefficientKernel r pi hirr hpi p q x y hp hq hx hy hrel
    have hpU : U p ≠ 0 := fun h => hp (U.injective (h.trans (map_zero U).symm))
    have hqU : U q ≠ 0 := fun h => hq (U.injective (h.trans (map_zero U).symm))
    refine ⟨U p, U q, hpU, hqU, ?_⟩
    exact (matrixCoefficientKernel_eq_of_intertwines r pi hirr hpi U hU p q hp hq).trans hpoint
  · exact matrixCoefficientKernelFamily_subset_component pi hpi x y hx hy

/-- Paper 5.10 on the received geometric spectrum: J_C is ker(pi) only after
identifying C with the whole coefficient-kernel family. -/
theorem geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    NormedSpace.geometricSpectrumKernel ℂ A
      (NormedSpace.toGeometricSpectrum ℂ A (matrixCoefficientKernel pi hpi x y hx hy)) =
        ((componentContinuousMap pi).ker : Set A) := by
  change {a : A | ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
    I ∈ (NormedSpace.geometricStructureClosure ℂ A).component
      (matrixCoefficientKernel pi hpi x y hx hy) → a ∈ I.val} = _
  rw [component_matrixCoefficientKernel_eq_family]
  exact setOf_forall_mem_matrixCoefficientKernelFamily_eq_ker pi hpi

/-- The same kernel identity on the actual gamma map, with no new primitive
spectrum or quotient relation introduced. This is a source interface for the
separate topological comparison. -/
theorem geometricSpectrumToPrimitive_toGeometricSpectrum_matrixCoefficientKernel_val
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    (NormedSpace.geometricSpectrumToPrimitive ℂ A
      (NormedSpace.toGeometricSpectrum ℂ A (matrixCoefficientKernel pi hpi x y hx hy))).val =
        ((componentContinuousMap pi).ker : Set A) := by
  rw [NormedSpace.geometricSpectrumToPrimitive_val]
  exact geometricSpectrumKernel_toGeometricSpectrum_matrixCoefficientKernel pi hpi x y hx hy

end MathlibAnnex.Analysis.CStarAlgebra.NonUnitalCStarRepresentation
