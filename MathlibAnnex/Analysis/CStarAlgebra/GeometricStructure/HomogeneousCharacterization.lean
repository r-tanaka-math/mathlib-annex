/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.GCRCharacterization
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartFiniteCharacter
import MathlibAnnex.Analysis.Normed.GeometricStructure.Separation
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite-dimensional irreducible representations and compact component models

The representation conditions are raw: finite dimensionality AND a predicate
on `finrank`. They do not define type I, and they never interpret the zero
`finrank` of an infinite-dimensional space as dimension zero. Taking the
predicate to be equality with `n` gives the homogeneous criterion; the bound
variant is in `SubhomogeneousCharacterization`.

A finite comparison has no full-continuity premise. Its promotion to a full
homeomorphism keeps its point map: first transfer finite dimension between the
actual normal parts, then apply the received finite-character theorem. This
includes dimensions one and two, without a projective semilinear lift.

The equivalences use compact models in the algebra universe. Separate
elimination theorems accept models in an arbitrary universe and conclude the
representation condition in EVERY independently specified Hilbert universe.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set

namespace ClosureSpace

attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra

/-- A finite comparison with a nonzero finite-dimensional compact-operator GSS,
with an additional predicate on the dimension. This is a geometric predicate,
not a definition of homogeneous representations. -/
def HasFiniteDimensionalCompactComparison.{uH, uX} {X : Type uX}
    (c : ClosureSpace X) (P : ℕ → Prop) : Prop :=
  ∃ (H : Type uH) (instN : NormedAddCommGroup H),
    letI := instN
    ∃ instI : InnerProductSpace ℂ H,
      letI := instI
      ∃ instC : CompleteSpace H,
        letI := instC
        ∃ instT : Nontrivial H,
          letI := instT
          FiniteDimensional ℂ H ∧ P (Module.finrank ℂ H) ∧
            Nonempty (FiniteHomeomorph c
              (NormedSpace.geometricStructureClosure ℂ
                (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)))

/-- The full-homeomorphism version retains a real finite-dimensional Hilbert
witness and the same dimension predicate. -/
def HasFiniteDimensionalCompactHomeomorph.{uH, uX} {X : Type uX}
    (c : ClosureSpace X) (P : ℕ → Prop) : Prop :=
  ∃ (H : Type uH) (instN : NormedAddCommGroup H),
    letI := instN
    ∃ instI : InnerProductSpace ℂ H,
      letI := instI
      ∃ instC : CompleteSpace H,
        letI := instC
        ∃ instT : Nontrivial H,
          letI := instT
          FiniteDimensional ℂ H ∧ P (Module.finrank ℂ H) ∧
            Nonempty (Homeomorph c
              (NormedSpace.geometricStructureClosure ℂ
                (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ H)))

universe uH uX
variable {X : Type uX} {c : ClosureSpace X} {P : ℕ → Prop}

/-- Forget only full continuity, not the finite-dimensional witness. -/
theorem HasFiniteDimensionalCompactHomeomorph.hasFiniteDimensionalCompactComparison
    (h : HasFiniteDimensionalCompactHomeomorph.{uH, uX} c P) :
    HasFiniteDimensionalCompactComparison.{uH, uX} c P := by
  obtain ⟨H, instN, instI, instC, instT, hdim, hP, ⟨e⟩⟩ := h
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  exact ⟨H, instN, instI, instC, instT, hdim, hP, ⟨e.toFiniteHomeomorph⟩⟩

/-- Every compact model in this predicate has positive dimension. In particular,
an empty target is not silently counted as a dimension-zero model. -/
theorem HasFiniteDimensionalCompactComparison.exists_pos_finrank
    (h : HasFiniteDimensionalCompactComparison.{uH, uX} c P) :
    ∃ m : ℕ, 0 < m ∧ P m := by
  obtain ⟨H, instN, instI, instC, instT, hdim, hP, _he⟩ := h
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  letI : FiniteDimensional ℂ H := hdim
  exact ⟨Module.finrank ℂ H, Module.finrank_pos, hP⟩

end ClosureSpace

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w
attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra
  HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

section Concrete
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transfer a genuine finite target dimension through the specified finite
map. No forward or inverse full continuity is an input. -/
theorem finite_and_finrank_eq_of_normalPart_compact_comparison
    [Nontrivial K] [FiniteDimensional ℂ K]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (e : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K))) :
    FiniteDimensional ℂ H ∧ Module.finrank ℂ H = Module.finrank ℂ K := by
  let T := ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K
  let f := e.trans (compactNormalPartHomeomorph (H := K)).symm.toFiniteHomeomorph
  have hd := finite_and_finrank_eq_of_normalPart_finiteHomeomorph S T hS
    (isIrreducible_compactOperatorRepresentation K) f
    (Or.inr (inferInstance : Module.Finite ℂ K))
  exact ⟨hd.1, hd.2.2⟩

/-- Promote this SAME finite comparison to a full homeomorphism. Only actual
coefficient kernels are used by the finite-character theorem. -/
theorem exists_homeomorph_eq_of_finiteDimensional_compact_comparison
    [Nontrivial K] [FiniteDimensional ℂ K]
    (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))]
    (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))
    (e : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K))) :
    ∃ F : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)),
      F.toEquiv = e.toEquiv := by
  letI : FiniteDimensional ℂ H :=
    (finite_and_finrank_eq_of_normalPart_compact_comparison S hS e).1
  let T := ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K
  letI : FiniteDimensional ℂ S := finiteDimensional_operator_subalgebra S
  letI : FiniteDimensional ℂ T := finiteDimensional_operator_subalgebra T
  let a := compactNormalPartHomeomorph (H := K)
  let f := e.trans a.symm.toFiniteHomeomorph
  refine ⟨(normalPartHomeomorphOfFiniteDimensional S T f).trans a, ?_⟩
  apply Equiv.ext
  intro I
  change a.toEquiv (a.toEquiv.symm (e.toEquiv I)) = e.toEquiv I
  exact a.toEquiv.apply_symm_apply (e.toEquiv I)

end Concrete

section Algebra
variable {A : Type u} [NonUnitalCStarAlgebra A] [hA : Nontrivial A]
attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

include hA in
/-- The SAME component comparison upgrades; the homeomorphism of a normal part
with the component (not its closure) cancels from the point-map formula. -/
theorem exists_component_homeomorph_eq_of_finiteDimensional_compact_comparison
    [Nontrivial K] [FiniteDimensional ℂ K]
    (I : NormedSpace.GeometricStructureSpace ℂ A)
    (e : ClosureSpace.FiniteHomeomorph
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K))) :
    ∃ F : ClosureSpace.Homeomorph
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I))
      (NormedSpace.geometricStructureClosure ℂ
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ K)),
      F.toEquiv = e.toEquiv := by
  obtain ⟨L, instN, instI, instC, pi, hpi, a, _ha⟩ :=
    exists_representation_normalPart_homeomorph_component A I
  letI := instN
  letI := instI
  letI := instC
  have hi := (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi
  obtain ⟨F, hF⟩ := exists_homeomorph_eq_of_finiteDimensional_compact_comparison
    (NonUnitalStarAlgHom.range pi) hi (a.toFiniteHomeomorph.trans e)
  refine ⟨a.symm.trans F, ?_⟩
  apply Equiv.ext
  intro J
  change F.toEquiv (a.toEquiv.symm J) = e.toEquiv J
  rw [hF]
  change e.toEquiv (a.toEquiv (a.toEquiv.symm J)) = e.toEquiv J
  rw [Equiv.apply_symm_apply]

include hA in
/-- Full and finite comparisons are equivalent on actual components with a
finite-dimensional compact target, even in an independent model universe. -/
theorem component_hasFiniteDimensionalCompactComparison_iff_homeomorph
    (P : ℕ → Prop) (I : NormedSpace.GeometricStructureSpace ℂ A) :
    ClosureSpace.HasFiniteDimensionalCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P ↔
      ClosureSpace.HasFiniteDimensionalCompactHomeomorph.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P := by
  constructor
  · rintro ⟨L, instN, instI, instC, instT, hdim, hP, ⟨e⟩⟩
    letI := instN
    letI := instI
    letI := instC
    letI := instT
    letI : FiniteDimensional ℂ L := hdim
    obtain ⟨F, _hF⟩ :=
      exists_component_homeomorph_eq_of_finiteDimensional_compact_comparison I e
    exact ⟨L, instN, instI, instC, instT, hdim, hP, ⟨F⟩⟩
  · exact ClosureSpace.HasFiniteDimensionalCompactHomeomorph.hasFiniteDimensionalCompactComparison

include hA in
/-- A comparison model in ANY fixed universe supplies both genuine finiteness
and the numerical dimension predicate in each small pure GNS model. -/
theorem forall_pure_state_finiteDimensional_finrank_of_component_compact_comparisons
    (P : ℕ → Prop)
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P) :
    ∀ phi : NonUnitalPureState A,
      FiniteDimensional ℂ phi.GNS ∧ P (Module.finrank ℂ phi.GNS) := by
  intro phi
  let pi := phi.gnsRepresentation
  let x := phi.gnsVector
  let I := NonUnitalCStarRepresentation.matrixCoefficientKernel pi
    phi.isIrreducible_gnsRepresentation x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  let a := imageNormalPartHomeomorph pi phi.isIrreducible_gnsRepresentation
    x x phi.gnsVector_ne_zero phi.gnsVector_ne_zero
  obtain ⟨L, instN, instI, instC, instT, hdim, hP, ⟨e⟩⟩ := h I
  letI := instN
  letI := instI
  letI := instC
  letI := instT
  letI : FiniteDimensional ℂ L := hdim
  have hi := (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2
    phi.isIrreducible_gnsRepresentation
  have hd := finite_and_finrank_eq_of_normalPart_compact_comparison (NonUnitalStarAlgHom.range pi) hi
    (a.toFiniteHomeomorph.trans e)
  exact ⟨hd.1, hd.2.symm ▸ hP⟩

include hA in
/-- Pure-state finite-dimensional tests are equivalent to finite compact
component models in the algebra universe. Exact interpolation gives
image = B(H) = K(H); the GNS component and its preimage homeomorphism are retained. -/
theorem forall_pure_state_finiteDimensional_finrank_iff_component_compact_comparison
    (P : ℕ → Prop) :
    (∀ phi : NonUnitalPureState A,
      FiniteDimensional ℂ phi.GNS ∧ P (Module.finrank ℂ phi.GNS)) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P := by
  constructor
  · intro h I
    obtain ⟨L, instN, instI, instC, pi, hpi, a, _ha⟩ :=
      exists_representation_normalPart_homeomorph_component A I
    letI := instN
    letI := instI
    letI := instC
    letI : Nontrivial L := pi.nontrivial_of_isNonzero hpi.1
    have hd := NonUnitalCStarRepresentation.finiteDimensional_finrank_of_forall_pure_state
      P h pi hpi
    letI : FiniteDimensional ℂ L := hd.1
    have hi := (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).2 hpi
    have hr : (NonUnitalStarAlgHom.range pi) = ContinuousLinearMap.compactOperatorStarSubalgebra ℂ L := by
      rw [eq_top_of_isIrreducible_subtype_of_finiteDimensional (NonUnitalStarAlgHom.range pi) hi,
        ContinuousLinearMap.compactOperatorStarSubalgebra_eq_top]
    obtain ⟨b⟩ := nonempty_homeomorph_compact_of_eq (NonUnitalStarAlgHom.range pi) hr
    exact ⟨L, instN, instI, instC, inferInstance, hd.1, hd.2,
      ⟨(a.symm.trans b).toFiniteHomeomorph⟩⟩
  · exact forall_pure_state_finiteDimensional_finrank_of_component_compact_comparisons P

include hA in
/-- The conclusion covers an arbitrary represented Hilbert universe; the
comparison models may inhabit yet another universe. -/
theorem finiteDimensional_finrank_of_component_compact_comparisons
    (P : ℕ → Prop)
    (h : ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P)
    (pi : NonUnitalCStarRepresentation A H) (hpi : pi.IsIrreducible) :
    FiniteDimensional ℂ H ∧ P (Module.finrank ℂ H) :=
  NonUnitalCStarRepresentation.finiteDimensional_finrank_of_forall_pure_state P
    (forall_pure_state_finiteDimensional_finrank_of_component_compact_comparisons P h) pi hpi

include hA in
/-- Raw all-representation condition in the small universe. The preceding
elimination theorem is its separately proved extension to every Hilbert universe. -/
theorem forall_irreducible_finiteDimensional_finrank_iff_component_compact_comparison
    (P : ℕ → Prop) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ P (Module.finrank ℂ L)) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P := by
  constructor
  · intro h
    apply (forall_pure_state_finiteDimensional_finrank_iff_component_compact_comparison P).1
    intro phi
    exact h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  · intro h L _ _ _ pi hpi
    exact finiteDimensional_finrank_of_component_compact_comparisons P h pi hpi

include hA in
/-- The same raw condition with full component homeomorphisms, obtained by
finite character, not by adding continuity assumptions to the finite comparison. -/
theorem forall_irreducible_finiteDimensional_finrank_iff_component_compact_homeomorph
    (P : ℕ → Prop) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ P (Module.finrank ℂ L)) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) P := by
  rw [forall_irreducible_finiteDimensional_finrank_iff_component_compact_comparison P]
  exact forall_congr' (fun I => component_hasFiniteDimensionalCompactComparison_iff_homeomorph P I)

include hA in
/-- Nontriviality supplies an actual GSS point and a nonzero pure GNS model.
Consequently every uniformly prescribed finite-dimension condition is realized
at a POSITIVE natural number. -/
theorem exists_pos_finrank_of_forall_pure_state (P : ℕ → Prop)
    (h : ∀ phi : NonUnitalPureState A,
      FiniteDimensional ℂ phi.GNS ∧ P (Module.finrank ℂ phi.GNS)) :
    ∃ m : ℕ, 0 < m ∧ P m := by
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨I, _hI⟩ := NormedSpace.exists_geometricStructureSpace_notMem ℂ A ha
  obtain ⟨phi, _hphi⟩ := NonUnitalPureState.toGeometricSpectrum_surjective
    (NormedSpace.toGeometricSpectrum ℂ A I)
  have hd := h phi
  letI : FiniteDimensional ℂ phi.GNS := hd.1
  letI : Nontrivial phi.GNS := phi.gnsRepresentation.nontrivial_of_isNonzero
    phi.isIrreducible_gnsRepresentation.1
  exact ⟨Module.finrank ℂ phi.GNS, Module.finrank_pos, hd.2⟩

include hA in
/-- The n-homogeneous criterion with n allowed to be zero, and explicit finite
dimensionality on the representation side. No independent Type-I bridge is used. -/
theorem forall_irreducible_finrank_eq_iff_component_compact_comparison (n : ℕ) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L = n) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m = n) :=
  forall_irreducible_finiteDimensional_finrank_iff_component_compact_comparison (fun m => m = n)

include hA in
/-- The full-homeomorphism form of the SAME homogeneous criterion. -/
theorem forall_irreducible_finrank_eq_iff_component_compact_homeomorph (n : ℕ) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L = n) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m = n) :=
  forall_irreducible_finiteDimensional_finrank_iff_component_compact_homeomorph (fun m => m = n)

include hA in
/-- Zero-homogeneity is impossible for a nontrivial algebra, through an actual
nonzero pure GNS model rather than a convention about infinite-dimensional finrank. -/
theorem not_forall_irreducible_finrank_eq_zero :
    ¬ (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L = 0) := by
  intro h
  obtain ⟨m, hm, hm0⟩ := exists_pos_finrank_of_forall_pure_state (fun m => m = 0)
    (fun phi => h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation)
  exact (Nat.ne_of_gt hm) hm0

include hA in
/-- No collection of zero-dimensional nonzero compact targets can model every
component. Model witnesses are allowed in any independently specified universe. -/
theorem not_forall_component_compact_comparison_finrank_zero :
    ¬ (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m = 0)) := by
  intro h
  obtain ⟨m, hm, hm0⟩ := exists_pos_finrank_of_forall_pure_state (fun m => m = 0)
    (forall_pure_state_finiteDimensional_finrank_of_component_compact_comparisons
      (fun m => m = 0) h)
  exact (Nat.ne_of_gt hm) hm0

end Algebra
end MathlibAnnex.Analysis.CStarAlgebra
