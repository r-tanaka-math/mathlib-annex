/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Primitive
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.AbsoluteState

/-!
# Independent spectral objects and their geometric comparison maps

Phi sends the unitary-equivalence class of an actual pure-state GNS action
to the component of that state's functional kernel. Psi retains the actual
primitive-ideal carrier. Their bijectivity is proved from the previously
established component representation and J_C identities. Neither source
spectrum is defined as an alias of, or transported from, a geometric spectrum.
No injectivity of kappa or gamma is assumed.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]
open NonUnitalCStarRepresentation

namespace NonUnitalPureState
variable {A}

/-- The functional kernel, as a point of the original general Banach GSS. -/
def geometricPoint (phi : NonUnitalPureState A) : NormedSpace.GeometricStructureSpace ℂ A :=
  extremeKernel ⟨phi.val, mem_extremePoints_dual_closedBall_of_isPureNonUnitalState
    phi.val phi.property⟩

/-- This point is exactly the canonical GNS vector-coefficient kernel. -/
theorem geometricPoint_eq_matrixCoefficientKernel (phi : NonUnitalPureState A) :
    phi.geometricPoint = matrixCoefficientKernel phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation phi.gnsVector phi.gnsVector
      phi.gnsVector_ne_zero phi.gnsVector_ne_zero := by
  apply Subtype.ext
  change (phi.val.ker : Set A) =
    ((matrixCoefficient phi.gnsRepresentation phi.gnsVector phi.gnsVector).ker : Set A)
  rw [phi.matrixCoefficient_gnsRepresentation]

/-- The actual component attached to a pure-state representation. -/
def toGeometricSpectrum (phi : NonUnitalPureState A) : NormedSpace.GeometricSpectrum ℂ A :=
  NormedSpace.toGeometricSpectrum ℂ A phi.geometricPoint

/-- Paper 5.8, with actual GNS equivalence, makes the comparison well-defined
and injective on the quotient. Functional-kernel equality is not the relation used. -/
theorem toGeometricSpectrum_eq_iff (phi psi : NonUnitalPureState A) :
    phi.toGeometricSpectrum = psi.toGeometricSpectrum ↔
      phi.gnsRepresentation.UnitaryEquivalent psi.gnsRepresentation := by
  change (NormedSpace.geometricStructureClosure ℂ A).toComponentPoint phi.geometricPoint =
    (NormedSpace.geometricStructureClosure ℂ A).toComponentPoint psi.geometricPoint ↔ _
  rw [ClosureSpace.toComponentPoint_eq_iff, phi.geometricPoint_eq_matrixCoefficientKernel,
    psi.geometricPoint_eq_matrixCoefficientKernel]
  exact related_matrixCoefficientKernel_iff_unitaryEquivalent
    phi.gnsRepresentation psi.gnsRepresentation
    phi.isIrreducible_gnsRepresentation psi.isIrreducible_gnsRepresentation
    phi.gnsVector phi.gnsVector psi.gnsVector psi.gnsVector
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero psi.gnsVector_ne_zero psi.gnsVector_ne_zero

/-- Every component contains a pure-state kernel, by the actual absolute-state construction. -/
theorem toGeometricSpectrum_surjective :
    Function.Surjective (toGeometricSpectrum (A := A)) := by
  intro C
  obtain ⟨rho, rfl⟩ := exists_toGeometricSpectrum_extremeKernel_eq C
  let phi : NonUnitalPureState A :=
    ⟨extremeAbsoluteState rho, isPureNonUnitalState_extremeAbsoluteState rho⟩
  refine ⟨phi, ?_⟩
  apply (ClosureSpace.toComponentPoint_eq_iff _ _ _).2
  exact (NormedSpace.geometricStructureClosure ℂ A).related_symm
    (related_extremeKernel_extremeAbsoluteState rho)

/-- The whole-component theorem, not a one-sided family inclusion, supplies J_C. -/
theorem geometricSpectrumToPrimitive_toGeometricSpectrum_val (phi : NonUnitalPureState A) :
    (NormedSpace.geometricSpectrumToPrimitive ℂ A phi.toGeometricSpectrum).val =
      (kernelIdeal phi.gnsRepresentation : Set A) := by
  rw [coe_kernelIdeal_eq_ker]
  exact geometricSpectrumToPrimitive_toGeometricSpectrum_pureStateKernel_val phi.val phi.property

end NonUnitalPureState

namespace IrreducibleSpectrum
variable {A}

/-- Phi is quotient elimination through the proved GNS-equivalence criterion. -/
def toGeometricSpectrum (q : IrreducibleSpectrum A) : NormedSpace.GeometricSpectrum ℂ A :=
  Quotient.lift NonUnitalPureState.toGeometricSpectrum
    (fun phi psi h => (phi.toGeometricSpectrum_eq_iff psi).2 h) q

@[simp]
theorem toGeometricSpectrum_ofPureState (phi : NonUnitalPureState A) :
    toGeometricSpectrum (ofPureState phi) = phi.toGeometricSpectrum := rfl

theorem toGeometricSpectrum_bijective : Function.Bijective (toGeometricSpectrum (A := A)) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro phi psi h
    exact Quotient.sound ((phi.toGeometricSpectrum_eq_iff psi).1 h)
  · intro C
    obtain ⟨phi, rfl⟩ := NonUnitalPureState.toGeometricSpectrum_surjective C
    exact ⟨ofPureState phi, rfl⟩

/-- Phi on an arbitrary represented Hilbert space, with the requested
component formula for every nonzero coefficient pair. -/
theorem toGeometricSpectrum_ofRepresentation
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible)
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    toGeometricSpectrum (ofRepresentation pi hpi) =
      NormedSpace.toGeometricSpectrum ℂ A (matrixCoefficientKernel pi hpi x y hx hy) := by
  let phi := (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose
  have hphi : pi.UnitaryEquivalent phi.gnsRepresentation :=
    (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose_spec
  change NormedSpace.toGeometricSpectrum ℂ A phi.geometricPoint = _
  rw [phi.geometricPoint_eq_matrixCoefficientKernel]
  apply (ClosureSpace.toComponentPoint_eq_iff _ _ _).2
  exact (related_matrixCoefficientKernel_iff_unitaryEquivalent
    phi.gnsRepresentation pi phi.isIrreducible_gnsRepresentation hpi
    phi.gnsVector phi.gnsVector x y
    phi.gnsVector_ne_zero phi.gnsVector_ne_zero hx hy).2 hphi.symm

/-- The bijection underlying Phi, before any topological conclusion. -/
def equivGeometricSpectrum : IrreducibleSpectrum A ≃ NormedSpace.GeometricSpectrum ℂ A :=
  Equiv.ofBijective toGeometricSpectrum toGeometricSpectrum_bijective

@[simp]
theorem equivGeometricSpectrum_ofPureState (phi : NonUnitalPureState A) :
    equivGeometricSpectrum (ofPureState phi) = phi.toGeometricSpectrum := rfl

end IrreducibleSpectrum

/-- Independently defined primitive kernels and geometric component intersections
are the same family of subsets of the original A. -/
theorem primitiveKernelFamily_eq_primitiveGeometricSpectrumFamily :
    primitiveKernelFamily A = NormedSpace.primitiveGeometricSpectrumFamily ℂ A := by
  ext P
  constructor
  · rintro ⟨phi, rfl⟩
    have h := (NormedSpace.geometricSpectrumToPrimitive ℂ A phi.toGeometricSpectrum).property
    rw [phi.geometricSpectrumToPrimitive_toGeometricSpectrum_val] at h
    exact h
  · intro hP
    let J : NormedSpace.PrimitiveGeometricSpectrum ℂ A := ⟨P, hP⟩
    obtain ⟨C, hC⟩ := NormedSpace.geometricSpectrumToPrimitive_surjective ℂ A J
    obtain ⟨phi, hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective C
    refine ⟨phi, ?_⟩
    calc
      (kernelIdeal phi.gnsRepresentation : Set A) =
          (NormedSpace.geometricSpectrumToPrimitive ℂ A phi.toGeometricSpectrum).val :=
        phi.geometricSpectrumToPrimitive_toGeometricSpectrum_val.symm
      _ = P := by rw [hphi, hC]

/-- Psi retains primitive-ideal carriers, with family membership justified by
an actual theorem rather than a definition of Prim in terms of PS. -/
def primitiveSpectrumEquivGeometric : PrimitiveSpectrum A ≃ NormedSpace.PrimitiveGeometricSpectrum ℂ A where
  toFun P := ⟨P.val, (primitiveKernelFamily_eq_primitiveGeometricSpectrumFamily A) ▸ P.property⟩
  invFun J := ⟨J.val, (primitiveKernelFamily_eq_primitiveGeometricSpectrumFamily A).symm ▸ J.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem primitiveSpectrumEquivGeometric_val (P : PrimitiveSpectrum A) :
    (primitiveSpectrumEquivGeometric A P).val = P.val := rfl

@[simp]
theorem primitiveSpectrumEquivGeometric_symm_val (J : NormedSpace.PrimitiveGeometricSpectrum ℂ A) :
    ((primitiveSpectrumEquivGeometric A).symm J).val = J.val := rfl

/-- The requested square, on actual points: Psi(kappa(q)) = gamma(Phi(q)). -/
theorem primitiveSpectrumEquivGeometric_kernel (q : IrreducibleSpectrum A) :
    primitiveSpectrumEquivGeometric A (IrreducibleSpectrum.kernel q) =
      NormedSpace.geometricSpectrumToPrimitive ℂ A (IrreducibleSpectrum.equivGeometricSpectrum q) := by
  refine Quotient.inductionOn q ?_
  intro phi
  apply Subtype.ext
  exact phi.geometricSpectrumToPrimitive_toGeometricSpectrum_val.symm

/-- Function-level square; neither vertical map is assumed injective. -/
theorem primitiveSpectrumEquivGeometric_comp_kernel :
    primitiveSpectrumEquivGeometric A ∘ IrreducibleSpectrum.kernel =
      NormedSpace.geometricSpectrumToPrimitive ℂ A ∘ IrreducibleSpectrum.equivGeometricSpectrum :=
  funext (primitiveSpectrumEquivGeometric_kernel A)

/-- The actual carrier relation used in the independent closure comparison. -/
theorem geometricSpectrumKernel_equivGeometricSpectrum (q : IrreducibleSpectrum A) :
    NormedSpace.geometricSpectrumKernel ℂ A (IrreducibleSpectrum.equivGeometricSpectrum q) =
      (IrreducibleSpectrum.kernel q).val :=
  (congrArg Subtype.val (primitiveSpectrumEquivGeometric_kernel A q)).symm

end MathlibAnnex.Analysis.CStarAlgebra
