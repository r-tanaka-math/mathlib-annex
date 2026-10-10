/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Representatives

/-!
# The primitive spectrum as a family of actual representation kernels

A point is an actual subset of A occurring as a pure-state GNS kernel. The
arbitrary-universe coverage theorem shows this is exactly the family of all
nonzero irreducible representation kernels. `toTwoSidedIdeal` proves and
exposes the algebraic ideal, rather than storing unproved ideal properties.
This definition is independent of the geometric primitive spectrum.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open NonUnitalCStarRepresentation

/-- A small list of the actual irreducible representation-kernel carriers. -/
def primitiveKernelFamily : Set (Set A) :=
  Set.range fun phi : NonUnitalPureState A => (kernelIdeal phi.gnsRepresentation : Set A)

/-- Actual primitive ideal carriers, not geometric primitive-spectrum points. -/
def PrimitiveSpectrum := {P : Set A // P ∈ primitiveKernelFamily A}

namespace PrimitiveSpectrum
variable {A}

/-- The primitive kernel of the actual GNS representation of a pure state. -/
def ofPureState (phi : NonUnitalPureState A) : PrimitiveSpectrum A :=
  ⟨(kernelIdeal phi.gnsRepresentation : Set A), phi, rfl⟩

theorem ofPureState_surjective : Function.Surjective (ofPureState (A := A)) := by
  rintro ⟨P, phi, hphi⟩
  exact ⟨phi, Subtype.ext hphi⟩

/-- An actual ideal underlying a primitive point; the subsequent carrier
identity makes this independent of the selected GNS witness. -/
def toTwoSidedIdeal (P : PrimitiveSpectrum A) : TwoSidedIdeal A :=
  kernelIdeal P.property.choose.gnsRepresentation

@[simp]
theorem coe_toTwoSidedIdeal (P : PrimitiveSpectrum A) :
    (P.toTwoSidedIdeal : Set A) = P.val := P.property.choose_spec

@[simp]
theorem mem_toTwoSidedIdeal (P : PrimitiveSpectrum A) (a : A) :
    a ∈ P.toTwoSidedIdeal ↔ a ∈ P.val := by
  rw [← P.coe_toTwoSidedIdeal]
  rfl

theorem toTwoSidedIdeal_ofPureState (phi : NonUnitalPureState A) :
    (ofPureState phi).toTwoSidedIdeal = kernelIdeal phi.gnsRepresentation := by
  apply SetLike.coe_injective
  exact coe_toTwoSidedIdeal (ofPureState phi)

theorem toTwoSidedIdeal_ne_top (P : PrimitiveSpectrum A) : P.toTwoSidedIdeal ≠ ⊤ :=
  kernelIdeal_ne_top _ P.property.choose.isIrreducible_gnsRepresentation.1

theorem val_ne_univ (P : PrimitiveSpectrum A) : P.val ≠ Set.univ := by
  intro h
  apply P.toTwoSidedIdeal_ne_top
  apply SetLike.coe_injective
  rw [P.coe_toTwoSidedIdeal, h, TwoSidedIdeal.coe_top]

theorem isClosed_val (P : PrimitiveSpectrum A) : IsClosed P.val := by
  rw [← P.coe_toTwoSidedIdeal]
  exact isClosed_kernelIdeal _

theorem star_mem_val_iff (P : PrimitiveSpectrum A) (a : A) :
    star a ∈ P.val ↔ a ∈ P.val := by
  rw [← P.coe_toTwoSidedIdeal]
  exact star_mem_kernelIdeal_iff _ a

theorem smul_mem_val (P : PrimitiveSpectrum A) (c : ℂ) {a : A} (ha : a ∈ P.val) :
    c • a ∈ P.val := by
  rw [← P.coe_toTwoSidedIdeal] at ha ⊢
  exact smul_mem_kernelIdeal _ c ha

/-- Meet-primality is proved, not a field in the primitive-point definition. -/
theorem inf_le_toTwoSidedIdeal_iff (P : PrimitiveSpectrum A) (I J : TwoSidedIdeal A) :
    I ⊓ J ≤ P.toTwoSidedIdeal ↔ I ≤ P.toTwoSidedIdeal ∨ J ≤ P.toTwoSidedIdeal :=
  inf_le_kernelIdeal_iff _ P.property.choose.isIrreducible_gnsRepresentation I J

/-- Any arbitrary-Hilbert-universe nonzero irreducible representation gives
an actual point of this primitive spectrum. -/
def ofRepresentation {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    PrimitiveSpectrum A := by
  refine ⟨(kernelIdeal pi : Set A), ?_⟩
  obtain ⟨phi, hphi⟩ := exists_pureState_kernelIdeal_eq pi hpi
  exact ⟨phi, congrArg SetLike.coe hphi.symm⟩

@[simp]
theorem ofRepresentation_val {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    (ofRepresentation pi hpi).val = (kernelIdeal pi : Set A) := rfl

end PrimitiveSpectrum

/-- No primitive ideal is the whole original algebra, including in the empty case. -/
theorem univ_notMem_primitiveKernelFamily : Set.univ ∉ primitiveKernelFamily A := by
  intro h
  exact (PrimitiveSpectrum.val_ne_univ (⟨Set.univ, h⟩ : PrimitiveSpectrum A)) rfl

namespace IrreducibleSpectrum
variable {A}

/-- The representation-kernel map kappa. Equivalent GNS models have equal
kernels, but its converse and injectivity are neither used nor asserted. -/
def kernel (q : IrreducibleSpectrum A) : PrimitiveSpectrum A :=
  Quotient.lift PrimitiveSpectrum.ofPureState
    (fun phi psi h => Subtype.ext (congrArg (fun I : TwoSidedIdeal A => (I : Set A))
      (NonUnitalCStarRepresentation.UnitaryEquivalent.kernelIdeal_eq h))) q

@[simp]
theorem kernel_ofPureState (phi : NonUnitalPureState A) :
    kernel (ofPureState phi) = PrimitiveSpectrum.ofPureState phi := rfl

/-- The abstract kernel map agrees with the concrete arbitrary-universe action. -/
theorem kernel_ofRepresentation {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    kernel (ofRepresentation pi hpi) = PrimitiveSpectrum.ofRepresentation pi hpi := by
  apply Subtype.ext
  exact congrArg (fun I : TwoSidedIdeal A => (I : Set A))
    (exists_pureState_unitaryEquivalent_gnsRepresentation pi hpi).choose_spec.kernelIdeal_eq.symm

theorem kernel_surjective : Function.Surjective (kernel (A := A)) := by
  intro P
  obtain ⟨phi, rfl⟩ := PrimitiveSpectrum.ofPureState_surjective P
  exact ⟨ofPureState phi, rfl⟩

end IrreducibleSpectrum
end MathlibAnnex.Analysis.CStarAlgebra
