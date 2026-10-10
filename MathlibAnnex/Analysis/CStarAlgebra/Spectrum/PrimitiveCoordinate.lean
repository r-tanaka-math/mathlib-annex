/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.Ideal.PrimitiveSeparation
import MathlibAnnex.Analysis.CStarAlgebra.Representation.CompactIntersection
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.CompactKernel
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.PrimitiveRepresentative
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Topology

/-!
# Isolated coordinates in a discrete primitive spectrum

For a primitive point `P`, the coordinate ideal is the intersection of every
other primitive kernel.  In a discrete primitive spectrum it survives outside
`P`, and the chosen pure-state GNS representation restricts faithfully and
nontrivially to it.  Under the representation-side CCR hypothesis, this
restriction has exactly the compact operators as range and is irreducible.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Set
open scoped CStarAlgebra BigOperators

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace PrimitiveSpectrum

/-- The intersection of all primitive kernels except `P`. -/
def coordinateIdeal (P : PrimitiveSpectrum A) : TwoSidedIdeal A :=
  kernelIntersection {Q : PrimitiveSpectrum A | Q ≠ P}

@[simp]
theorem mem_coordinateIdeal (P : PrimitiveSpectrum A) (a : A) :
    a ∈ P.coordinateIdeal ↔
      ∀ Q : PrimitiveSpectrum A, Q ≠ P → a ∈ Q.val := by
  simp only [coordinateIdeal, mem_kernelIntersection, Set.mem_setOf_eq]

/-- The coordinate ideal is norm closed as an arbitrary intersection of
representation kernels. -/
theorem isClosed_coordinateIdeal (P : PrimitiveSpectrum A) :
    IsClosed (P.coordinateIdeal : Set A) := by
  have hcarrier : (P.coordinateIdeal : Set A) =
      ⋂ Q : {Q : PrimitiveSpectrum A // Q ≠ P}, Q.1.val := by
    ext a
    change (a ∈ P.coordinateIdeal) ↔ _
    simp only [mem_coordinateIdeal, Set.mem_iInter, Subtype.forall]
  rw [hcarrier]
  exact isClosed_iInter fun Q => Q.1.isClosed_val

@[simp]
theorem star_mem_coordinateIdeal_iff (P : PrimitiveSpectrum A) (a : A) :
    star a ∈ P.coordinateIdeal ↔ a ∈ P.coordinateIdeal := by
  simp only [mem_coordinateIdeal]
  constructor
  · intro h Q hQP
    exact (Q.star_mem_val_iff a).1 (h Q hQP)
  · intro h Q hQP
    exact (Q.star_mem_val_iff a).2 (h Q hQP)

/-- Complex scalar closure, which is not contained in the bare algebraic
`TwoSidedIdeal` structure. -/
theorem smul_mem_coordinateIdeal (P : PrimitiveSpectrum A) (c : ℂ)
    {a : A} (ha : a ∈ P.coordinateIdeal) : c • a ∈ P.coordinateIdeal := by
  rw [mem_coordinateIdeal] at ha ⊢
  intro Q hQP
  exact Q.smul_mem_val c (ha Q hQP)

/-- The same carrier bundled as a nonunital star subalgebra. -/
def coordinateStarSubalgebra (P : PrimitiveSpectrum A) : NonUnitalStarSubalgebra ℂ A where
  carrier := P.coordinateIdeal
  zero_mem' := P.coordinateIdeal.zero_mem
  add_mem' := fun ha hb => P.coordinateIdeal.add_mem ha hb
  mul_mem' := fun ha hb => P.coordinateIdeal.mul_mem_right _ _ ha
  smul_mem' := fun c _ ha => P.smul_mem_coordinateIdeal c ha
  star_mem' := fun ha => (P.star_mem_coordinateIdeal_iff _).2 ha

@[simp]
theorem mem_coordinateStarSubalgebra (P : PrimitiveSpectrum A) (a : A) :
    a ∈ P.coordinateStarSubalgebra ↔ a ∈ P.coordinateIdeal := Iff.rfl

instance instNonUnitalCStarAlgebraCoordinateStarSubalgebra (P : PrimitiveSpectrum A) :
    NonUnitalCStarAlgebra P.coordinateStarSubalgebra :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra P.coordinateStarSubalgebra
    (h_closed := P.isClosed_coordinateIdeal)

/-- The chosen GNS representation restricted to the isolated coordinate ideal. -/
def coordinateRepresentation (P : PrimitiveSpectrum A) :
    NonUnitalCStarRepresentation P.coordinateStarSubalgebra
      P.pureStateRepresentative.GNS :=
  P.pureStateRepresentative.gnsRepresentation.comp
    (NonUnitalStarSubalgebraClass.subtype P.coordinateStarSubalgebra)

@[simp]
theorem coordinateRepresentation_apply (P : PrimitiveSpectrum A)
    (a : P.coordinateStarSubalgebra) :
    P.coordinateRepresentation a = P.pureStateRepresentative.gnsRepresentation a.1 := rfl

@[simp]
theorem mem_kernelIdeal_coordinateRepresentation (P : PrimitiveSpectrum A)
    (a : P.coordinateStarSubalgebra) :
    a ∈ NonUnitalCStarRepresentation.kernelIdeal P.coordinateRepresentation ↔
      a.1 ∈ P.toTwoSidedIdeal := by
  rw [NonUnitalCStarRepresentation.mem_kernelIdeal]
  change P.pureStateRepresentative.gnsRepresentation a.1 = 0 ↔ _
  rw [← NonUnitalCStarRepresentation.mem_kernelIdeal,
    kernelIdeal_pureStateRepresentative]

/-- The intersection of every actual primitive kernel is zero.  This is the
closed-ideal separation theorem specialized to the zero ideal. -/
theorem kernelIntersection_univ_eq_bot :
    kernelIntersection (Set.univ : Set (PrimitiveSpectrum A)) = ⊥ := by
  have hbotClosed : IsClosed ((⊥ : TwoSidedIdeal A) : Set A) := by
    simpa only [TwoSidedIdeal.coe_bot] using (isClosed_singleton : IsClosed ({0} : Set A))
  apply TwoSidedIdeal.ext
  intro a
  constructor
  · intro ha
    rw [TwoSidedIdeal.mem_bot]
    apply (mem_iff_forall_isIrreducible_of_ker_ge (⊥ : TwoSidedIdeal A)
      hbotClosed a).2
    intro H _instN _instI _instC rho hrho _hbot
    have hP := (mem_kernelIntersection (Set.univ : Set (PrimitiveSpectrum A)) a).1 ha
      (ofRepresentation rho hrho) (Set.mem_univ _)
    apply (NonUnitalCStarRepresentation.mem_kernelIdeal rho a).1
    change a ∈ (ofRepresentation rho hrho).val
    exact hP
  · intro ha
    rw [TwoSidedIdeal.mem_bot] at ha
    subst a
    exact (kernelIntersection (Set.univ : Set (PrimitiveSpectrum A))).zero_mem

/-- The isolated-coordinate ideal intersects its own primitive kernel only in
zero. -/
theorem coordinateIdeal_inf_toTwoSidedIdeal_eq_bot (P : PrimitiveSpectrum A) :
    P.coordinateIdeal ⊓ P.toTwoSidedIdeal = ⊥ := by
  apply le_antisymm
  · intro a ha
    have hall : a ∈ kernelIntersection (Set.univ : Set (PrimitiveSpectrum A)) := by
      rw [mem_kernelIntersection]
      intro Q _hQ
      by_cases hQP : Q = P
      · subst Q
        exact (mem_toTwoSidedIdeal P a).1 ha.2
      · exact (mem_coordinateIdeal P a).1 ha.1 Q hQP
    rw [kernelIntersection_univ_eq_bot] at hall
    exact hall
  · exact bot_le

/-- Discreteness forces the intersection of the other primitive kernels not
to be contained in `P`. -/
theorem not_coordinateIdeal_le_toTwoSidedIdeal
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A) :
    ¬ P.coordinateIdeal ≤ P.toTwoSidedIdeal := by
  intro hle
  have hmem : P ∈ closure {Q : PrimitiveSpectrum A | Q ≠ P} :=
    (mem_closure_primitiveSpectrum_iff A _ P).2 hle
  have hclosed : IsClosed {Q : PrimitiveSpectrum A | Q ≠ P} := isClosed_discrete _
  rw [hclosed.closure_eq] at hmem
  exact hmem rfl

/-- A concrete coordinate element survives in the selected primitive quotient. -/
theorem exists_mem_coordinateIdeal_not_mem_toTwoSidedIdeal
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A) :
    ∃ a : A, a ∈ P.coordinateIdeal ∧ a ∉ P.toTwoSidedIdeal := by
  by_contra! h
  exact P.not_coordinateIdeal_le_toTwoSidedIdeal h

/-- The restricted representation has zero kernel. -/
theorem kernelIdeal_coordinateRepresentation_eq_bot
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A) :
    NonUnitalCStarRepresentation.kernelIdeal P.coordinateRepresentation = ⊥ := by
  apply TwoSidedIdeal.ext
  intro a
  constructor
  · intro ha
    rw [TwoSidedIdeal.mem_bot]
    apply Subtype.ext
    have hboth : a.1 ∈ P.coordinateIdeal ⊓ P.toTwoSidedIdeal :=
      ⟨a.2, (mem_kernelIdeal_coordinateRepresentation P a).1 ha⟩
    rw [coordinateIdeal_inf_toTwoSidedIdeal_eq_bot] at hboth
    rw [TwoSidedIdeal.mem_bot] at hboth
    exact hboth
  · intro ha
    rw [TwoSidedIdeal.mem_bot] at ha
    subst a
    exact (NonUnitalCStarRepresentation.kernelIdeal P.coordinateRepresentation).zero_mem

/-- Faithfulness of the actual restriction. -/
theorem coordinateRepresentation_injective
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A) :
    Function.Injective P.coordinateRepresentation := by
  intro a b hab
  have hz : P.coordinateRepresentation (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hm : a - b ∈ NonUnitalCStarRepresentation.kernelIdeal
      P.coordinateRepresentation :=
    (NonUnitalCStarRepresentation.mem_kernelIdeal _ _).2 hz
  rw [kernelIdeal_coordinateRepresentation_eq_bot, TwoSidedIdeal.mem_bot] at hm
  exact sub_eq_zero.mp hm

/-- The restriction is genuinely nonzero. -/
theorem isNonzero_coordinateRepresentation
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A) :
    P.coordinateRepresentation.IsNonzero := by
  obtain ⟨a, haJ, haP⟩ := P.exists_mem_coordinateIdeal_not_mem_toTwoSidedIdeal
  refine ⟨⟨a, haJ⟩, ?_⟩
  intro hz
  exact haP ((mem_kernelIdeal_coordinateRepresentation P ⟨a, haJ⟩).2
    ((NonUnitalCStarRepresentation.mem_kernelIdeal _ _).2 hz))

/-- Every rank-one operator belongs to the restricted image under the CCR
hypothesis for the selected GNS representation. -/
theorem rankOne_mem_coordinateRepresentation_range
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A)
    (hCCR : (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS)
    (u v : P.pureStateRepresentative.GNS) :
    InnerProductSpace.rankOne ℂ u v ∈ (NonUnitalStarAlgHom.range P.coordinateRepresentation) := by
  classical
  let pi := P.pureStateRepresentative.gnsRepresentation
  obtain ⟨j, hjJ, hjP⟩ := P.exists_mem_coordinateIdeal_not_mem_toTwoSidedIdeal
  have hj0 : pi j ≠ 0 := by
    intro hz
    exact hjP ((NonUnitalCStarRepresentation.mem_kernelIdeal pi j).2 hz)
  obtain ⟨x, hx⟩ : ∃ x : P.pureStateRepresentative.GNS, pi j x ≠ 0 := by
    by_contra! h
    exact hj0 (ContinuousLinearMap.ext h)
  let c : ℂ := inner ℂ (pi j x) (pi j x)
  have hc : c ≠ 0 := by
    intro hc0
    exact hx (inner_self_eq_zero.mp hc0)
  let L : P.pureStateRepresentative.GNS →L[ℂ] P.pureStateRepresentative.GNS :=
    InnerProductSpace.rankOne ℂ (c⁻¹ • u) (pi j x)
  let R : P.pureStateRepresentative.GNS →L[ℂ] P.pureStateRepresentative.GNS :=
    InnerProductSpace.rankOne ℂ x v
  have hLK : IsCompactOperator L := InnerProductSpace.isCompactOperator_rankOne _ _
  have hRK : IsCompactOperator R := InnerProductSpace.isCompactOperator_rankOne _ _
  have hLrange : L ∈ (NonUnitalStarAlgHom.range pi) := by
    rw [hCCR]
    exact hLK
  have hRrange : R ∈ (NonUnitalStarAlgHom.range pi) := by
    rw [hCCR]
    exact hRK
  obtain ⟨l, hl⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hLrange
  obtain ⟨r, hr⟩ := (NonUnitalStarAlgHom.mem_range pi).1 hRrange
  apply (NonUnitalStarAlgHom.mem_range P.coordinateRepresentation).2
  refine ⟨⟨l * j * r, ?_⟩, ?_⟩
  · exact P.coordinateIdeal.mul_mem_right (l * j) r
      (P.coordinateIdeal.mul_mem_left l j hjJ)
  · change pi (l * j * r) = InnerProductSpace.rankOne ℂ u v
    rw [map_mul, map_mul, hl, hr]
    change (L * pi j) * R = _
    rw [InnerProductSpace.rankOne_mul_mul_rankOne]
    ext z
    simp only [L, R, c, ContinuousLinearMap.smul_apply,
      InnerProductSpace.rankOne_apply, smul_smul]
    change (c * (inner ℂ v z * c⁻¹)) • u = inner ℂ v z • u
    rw [mul_comm (inner ℂ v z) c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- Every compact operator has an actual preimage in the coordinate ideal. -/
theorem compactOperatorStarSubalgebra_le_coordinateRepresentation_range
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A)
    (hCCR : (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS) :
    ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS ≤ (NonUnitalStarAlgHom.range P.coordinateRepresentation) := by
  letI : PartialOrder P.coordinateStarSubalgebra := _root_.CStarAlgebra.spectralOrder _
  letI : StarOrderedRing P.coordinateStarSubalgebra := _root_.CStarAlgebra.spectralOrderedRing _
  intro T hT
  apply closure_minimal
    (t := ((NonUnitalStarAlgHom.range P.coordinateRepresentation) :
      Set (P.pureStateRepresentative.GNS →L[ℂ] P.pureStateRepresentative.GNS)))
    ?_ (HomKernelQuotient.isClosed_image P.coordinateRepresentation)
    hT.mem_closure_setOf_finiteDimensional_range
  intro F hF
  change FiniteDimensional ℂ F.toLinearMap.range at hF
  letI : FiniteDimensional ℂ F.toLinearMap.range := hF
  obtain ⟨n, u, v, hsum⟩ := F.exists_sum_rankOne_eq_of_finiteDimensional_range
  rw [← hsum]
  exact sum_mem fun i _ => P.rankOne_mem_coordinateRepresentation_range hCCR (u i) (v i)

/-- Exact image formula for the isolated coordinate restriction. -/
theorem coordinateRepresentation_range_eq_compactOperatorStarSubalgebra
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A)
    (hCCR : (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS) :
    (NonUnitalStarAlgHom.range P.coordinateRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS := by
  apply le_antisymm
  · intro T hT
    obtain ⟨a, rfl⟩ := (NonUnitalStarAlgHom.mem_range P.coordinateRepresentation).1 hT
    rw [← hCCR]
    exact (NonUnitalStarAlgHom.mem_range P.pureStateRepresentative.gnsRepresentation).2
      ⟨a.1, rfl⟩
  · exact P.compactOperatorStarSubalgebra_le_coordinateRepresentation_range hCCR

/-- The faithful isolated-coordinate restriction is itself irreducible. -/
theorem isIrreducible_coordinateRepresentation
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A)
    (hCCR : (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS) :
    P.coordinateRepresentation.IsIrreducible := by
  have hnz := P.isNonzero_coordinateRepresentation
  letI : Nontrivial P.pureStateRepresentative.GNS :=
    NonUnitalCStarRepresentation.nontrivial_of_isNonzero P.coordinateRepresentation hnz
  refine ⟨hnz, ?_⟩
  intro L hL
  apply (isIrreducible_compactOperatorRepresentation
    P.pureStateRepresentative.GNS).2 L
  refine ⟨hL.1, ?_⟩
  intro T x hx
  have hT : (T : P.pureStateRepresentative.GNS →L[ℂ]
      P.pureStateRepresentative.GNS) ∈ (NonUnitalStarAlgHom.range P.coordinateRepresentation) := by
    rw [P.coordinateRepresentation_range_eq_compactOperatorStarSubalgebra hCCR]
    exact T.property
  obtain ⟨a, ha⟩ := (NonUnitalStarAlgHom.mem_range P.coordinateRepresentation).1 hT
  change (T : P.pureStateRepresentative.GNS →L[ℂ]
    P.pureStateRepresentative.GNS) x ∈ L ∧
    (ContinuousLinearMap.adjoint (T : P.pureStateRepresentative.GNS →L[ℂ]
      P.pureStateRepresentative.GNS)) x ∈ L
  rw [← ha]
  exact hL.2 a x hx

/-- The selected primitive kernel is the kernel of the ambient GNS action,
while the coordinate restriction has zero kernel and compact image. -/
theorem coordinateRepresentation_spec
    [DiscreteTopology (PrimitiveSpectrum A)] (P : PrimitiveSpectrum A)
    (hCCR : (NonUnitalStarAlgHom.range P.pureStateRepresentative.gnsRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS) :
    NonUnitalCStarRepresentation.kernelIdeal
        P.pureStateRepresentative.gnsRepresentation = P.toTwoSidedIdeal ∧
    NonUnitalCStarRepresentation.kernelIdeal P.coordinateRepresentation = ⊥ ∧
    (NonUnitalStarAlgHom.range P.coordinateRepresentation) =
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ
        P.pureStateRepresentative.GNS ∧
    P.coordinateRepresentation.IsIrreducible := by
  exact ⟨kernelIdeal_pureStateRepresentative P,
    P.kernelIdeal_coordinateRepresentation_eq_bot,
    P.coordinateRepresentation_range_eq_compactOperatorStarSubalgebra hCCR,
    P.isIrreducible_coordinateRepresentation hCCR⟩

end PrimitiveSpectrum

end MathlibAnnex.Analysis.CStarAlgebra
