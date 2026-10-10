/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIdealRigidity
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Primitive

/-!
# Kernel-map injectivity under compact-containing representation images

The local representation theorem is proved first; this module applies it to
the independently defined spectrum. No global Type-I equivalence is imported.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set InnerProductSpace
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
open NonUnitalCStarRepresentation

namespace IrreducibleSpectrum
variable {A : Type w} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- GCR kernel-map injectivity, obtained from rank-one rigidity and actual
kernel quotient descent, not from a Glimm--Sakai axiom. Small pure GNS tests
are explicit; all other Hilbert universes are covered by the preceding
pointwise unitary theorem. -/
theorem kernel_injective_of_forall_pure_state_compact_le_range
    (hK : ∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤ NonUnitalStarAlgHom.range phi.gnsRepresentation) :
    Function.Injective (kernel : IrreducibleSpectrum A → PrimitiveSpectrum A) := by
  intro p q hpq
  obtain ⟨phi, rfl⟩ := ofPureState_surjective p
  obtain ⟨psi, rfl⟩ := ofPureState_surjective q
  have hker : kernelIdeal phi.gnsRepresentation = kernelIdeal psi.gnsRepresentation := by
    apply SetLike.coe_injective
    exact congrArg Subtype.val hpq
  apply (ofPureState_eq_iff phi psi).2
  exact NonUnitalCStarRepresentation.unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
    phi.gnsRepresentation psi.gnsRepresentation psi.isIrreducible_gnsRepresentation hker (hK phi)

/-- Surjectivity was already available independently; combine it only now
with the proved local injectivity. -/
theorem kernel_bijective_of_forall_pure_state_compact_le_range
    (hK : ∀ phi : NonUnitalPureState A,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤ NonUnitalStarAlgHom.range phi.gnsRepresentation) :
    Function.Bijective (kernel : IrreducibleSpectrum A → PrimitiveSpectrum A) :=
  ⟨kernel_injective_of_forall_pure_state_compact_le_range hK, kernel_surjective⟩

/-- Exact representation-side CCR consequence. The image equality assumption
is not silently weakened to mere containment IN the compacts. -/
theorem kernel_injective_of_forall_pure_state_range_eq_compact
    (hK : ∀ phi : NonUnitalPureState A,
      NonUnitalStarAlgHom.range phi.gnsRepresentation = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS) :
    Function.Injective (kernel : IrreducibleSpectrum A → PrimitiveSpectrum A) :=
  kernel_injective_of_forall_pure_state_compact_le_range (fun phi => (hK phi).ge)

end IrreducibleSpectrum
end MathlibAnnex.Analysis.CStarAlgebra
