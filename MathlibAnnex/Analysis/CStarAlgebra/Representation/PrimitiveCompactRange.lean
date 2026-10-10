/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.PrimitiveRepresentative
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIdealRigidity
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactRange

/-!
# Compact range tests at primitive pure-state representatives

These bridges require neither a compact representation of the algebra nor a
 discrete primitive spectrum. The selected GNS condition yields a genuine
unitary equivalence by compact containment and equal-kernel rigidity. The
Hilbert-universe lift, the pure-GNS tests, and the algebra-universe test are
kept distinct. The two sections preserve the authors' original literal
scope and type binders; no second representation or CCR predicate is defined.
-/

@[expose] public section

section
set_option autoImplicit false
noncomputable section

open Set InnerProductSpace
open scoped CStarAlgebra Topology

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace NonUnitalCStarRepresentation

/-- At the primitive kernel of an arbitrary irreducible action, compact
containment of the selected representative's range yields an actual unitary
intertwiner. Equal kernels alone are not sufficient and are not used alone. -/
theorem pureStateRepresentative_unitaryEquivalent_of_range_eq_compact
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible)
    (hcompact : (NonUnitalStarAlgHom.range (PrimitiveSpectrum.ofRepresentation rho hrho).pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        (PrimitiveSpectrum.ofRepresentation rho hrho).pureStateRepresentative.GNS) :
    (PrimitiveSpectrum.ofRepresentation rho hrho).pureStateRepresentative.gnsRepresentation.UnitaryEquivalent rho := by
  let P := PrimitiveSpectrum.ofRepresentation rho hrho
  have hker : kernelIdeal P.pureStateRepresentative.gnsRepresentation = kernelIdeal rho := by
    apply SetLike.coe_injective
    calc
      (kernelIdeal P.pureStateRepresentative.gnsRepresentation : Set A) = P.val :=
        P.coe_kernelIdeal_pureStateRepresentative
      _ = (kernelIdeal rho : Set A) := rfl
  exact unitaryEquivalent_of_kernelIdeal_eq_of_compact_le_range
    P.pureStateRepresentative.gnsRepresentation rho hrho hker hcompact.ge

/-- The selected primitive GNS compact-range condition lifts to any
irreducible representation in an independent Hilbert universe. The lifting
proof includes the unitary construction, not just a kernel comparison. -/
theorem range_eq_compact_of_forall_pureStateRepresentative_range_eq_compact
    (hcompact : ∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ P.pureStateRepresentative.GNS)
    (rho : NonUnitalCStarRepresentation A K) (hrho : rho.IsIrreducible) :
    (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  let P := PrimitiveSpectrum.ofRepresentation rho hrho
  exact (pureStateRepresentative_unitaryEquivalent_of_range_eq_compact rho hrho
    (hcompact P)).range_eq_compactOperatorStarSubalgebra (hcompact P)

end NonUnitalCStarRepresentation

/-- The selected primitive tests and all pure-state GNS tests are equivalent.
The preceding universe-polymorphic lifting lemma additionally supplies the
CCR conclusion on every irreducible Hilbert space, not merely the GNS fibers. -/
theorem forall_pureState_range_eq_compact_iff_forall_pureStateRepresentative_range_eq_compact :
    (∀ phi : NonUnitalPureState A, (NonUnitalStarAlgHom.range phi.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS) ↔
    (∀ P : PrimitiveSpectrum A, (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ P.pureStateRepresentative.GNS) := by
  constructor
  · intro h P
    exact h P.pureStateRepresentative
  · intro h phi
    exact NonUnitalCStarRepresentation.range_eq_compact_of_forall_pureStateRepresentative_range_eq_compact
        h phi.gnsRepresentation phi.isIrreducible_gnsRepresentation

end MathlibAnnex.Analysis.CStarAlgebra
end
end

section
set_option autoImplicit false
noncomputable section

open Set
open scoped Classical CStarAlgebra ENNReal lp

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

namespace MathlibAnnex.Analysis.CStarAlgebra

open MathlibAnnex.Analysis.InnerProductSpace

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A]

namespace PrimitiveSpectrum

/-- The all-irreducible compact range hypothesis applies to each selected
primitive GNS action, using its already proved irreducibility.  Only its
instance in the universe of `A` is needed. -/
theorem range_pureStateRepresentative_eq_compact_of_forall_irreducible_range_eq_compact
    (hCCR : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
      rho.IsIrreducible →
        (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)
    (P : PrimitiveSpectrum A) :
    (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS :=
  hCCR P.pureStateRepresentative.GNS
    P.pureStateRepresentative.gnsRepresentation
    P.pureStateRepresentative.isIrreducible_gnsRepresentation

/-- The selected range condition is equivalent to the all-irreducible test in
the universe of the algebra.  The preceding pointwise theorem extends the
forward implication to arbitrary Hilbert universes, without a universe-lifting
assumption.  Neither implication requires a discrete primitive spectrum. -/
theorem forall_pureStateRepresentative_range_eq_compact_iff_forall_irreducible_range_eq_compact :
    (∀ P : PrimitiveSpectrum A,
      (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
        ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
          P.pureStateRepresentative.GNS) ↔
    ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (rho : NonUnitalCStarRepresentation A K),
      rho.IsIrreducible →
        (NonUnitalStarAlgHom.range rho) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K := by
  constructor
  · intro hSelected K _ _ _ rho hrho
    exact
      NonUnitalCStarRepresentation.range_eq_compact_of_forall_pureStateRepresentative_range_eq_compact
        hSelected rho hrho
  · intro hCCR P
    exact range_pureStateRepresentative_eq_compact_of_forall_irreducible_range_eq_compact
      hCCR P

end PrimitiveSpectrum
end MathlibAnnex.Analysis.CStarAlgebra
end
end
