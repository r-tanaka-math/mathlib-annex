/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.HomogeneousCharacterization

/-!
# Uniform finite bounds on irreducible representation dimensions

These are raw representation-side subhomogeneous criteria, not a new definition
of type I or a substitute for the independent Glimm--Sakai bridge. The common
finite-dimensional comparison proof is reused with the predicate `m ≤ n`.
Every representation condition includes finiteness, and n = 0 is treated by a
nonzero pure GNS witness. The zero C-star algebra is outside this module's scope.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u w
variable {A : Type u} [NonUnitalCStarAlgebra A] [hA : Nontrivial A]
attribute [local instance] ContinuousLinearMap.isClosed_compactOperatorStarSubalgebra
  _root_.CStarAlgebra.spectralOrder _root_.CStarAlgebra.spectralOrderedRing

include hA in
/-- A uniform finite bound on all irreducible dimensions is equivalent to
finite compact component models satisfying that bound. Neither direction of
full continuity is a premise on the finite comparisons. -/
theorem forall_irreducible_finrank_le_iff_component_compact_comparison (n : ℕ) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L ≤ n) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m ≤ n) :=
  forall_irreducible_finiteDimensional_finrank_iff_component_compact_comparison (fun m => m ≤ n)

include hA in
/-- Full homeomorphisms give the same bounded-dimension condition. The full
continuity was proved from finite character in the common theorem. -/
theorem forall_irreducible_finrank_le_iff_component_compact_homeomorph (n : ℕ) :
    (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L ≤ n) ↔
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactHomeomorph.{u, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m ≤ n) :=
  forall_irreducible_finiteDimensional_finrank_iff_component_compact_homeomorph (fun m => m ≤ n)

include hA in
/-- There is no zero bound on the finite dimensions of all nonzero irreducible
representations of a nontrivial C-star algebra. -/
theorem not_forall_irreducible_finrank_le_zero :
    ¬ (∀ (L : Type u) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L],
      ∀ pi : NonUnitalCStarRepresentation A L, pi.IsIrreducible →
        FiniteDimensional ℂ L ∧ Module.finrank ℂ L ≤ 0) := by
  intro h
  obtain ⟨m, hm, hm0⟩ := exists_pos_finrank_of_forall_pure_state (fun m => m ≤ 0)
    (fun phi => h phi.GNS phi.gnsRepresentation phi.isIrreducible_gnsRepresentation)
  exact (lt_irrefl (0 : ℕ)) (lt_of_lt_of_le hm hm0)

include hA in
/-- The bounded component condition is also impossible at n = 0, even if
compact target carriers may inhabit a separate universe. -/
theorem not_forall_component_compact_comparison_finrank_le_zero :
    ¬ (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactComparison.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m ≤ 0)) := by
  intro h
  obtain ⟨m, hm, hm0⟩ := exists_pos_finrank_of_forall_pure_state (fun m => m ≤ 0)
    (forall_pure_state_finiteDimensional_finrank_of_component_compact_comparisons
      (fun m => m ≤ 0) h)
  exact (lt_irrefl (0 : ℕ)) (lt_of_lt_of_le hm hm0)

include hA in
/-- The full compact-model condition cannot have zero dimension or a zero
upper bound. This is a consequence of the real nonzero witnesses, not vacuity. -/
theorem not_forall_component_compact_homeomorph_finrank_le_zero :
    ¬ (∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ClosureSpace.HasFiniteDimensionalCompactHomeomorph.{w, u}
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)) (fun m => m ≤ 0)) := by
  intro h
  exact not_forall_component_compact_comparison_finrank_le_zero
    (fun I => (h I).hasFiniteDimensionalCompactComparison)

end MathlibAnnex.Analysis.CStarAlgebra
