/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.LinearAlgebra.FiniteDimensional.FiniteIntersection
public import MathlibAnnex.Topology.ClosureSpace.FiniteCharacter
public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# Relative hull-kernel finite character over a finite-dimensional ambient space

Only the selected relative points are required to be actual linear subspaces.
Other ambient hull-kernel points remain arbitrary sets.
-/

@[expose] public section
set_option autoImplicit false

universe u v w
namespace ClosureSpace.HullKernel
variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {V : Type v} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- Relative hull-kernel closure is finitely determined when each point of
the relative family is an actual linear subspace. The ambient family itself
may contain nonlinear sets. -/
theorem exists_finite_subset_subspace_closure_eq
    (F : Set (Set V)) (hF : Set.univ ∉ F) (G : Set F)
    (P : G → Submodule 𝕜 V) (hP : ∀ I : G, (P I : Set V) = I.val.val)
    (s : Set G) :
    ∃ t : Set G, t ⊆ s ∧ t.Finite ∧
      ((space F hF).subspace G).closure t = ((space F hF).subspace G).closure s := by
  have hk (t : Set G) : kernel F (Subtype.val '' t) = ⋂ I ∈ t, (P I : Set V) := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iInter.mpr
      intro I
      apply Set.mem_iInter.mpr
      intro hI
      rw [hP I]
      exact hx I.val ⟨I, hI, rfl⟩
    · intro hx I hI
      rcases hI with ⟨J, hJ, rfl⟩
      rw [← hP J]
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hx J) hJ
  obtain ⟨t, hts, ht, heq⟩ :=
    Submodule.exists_finite_subset_iInter_eq_of_finiteDimensional P s
  refine ⟨t, hts, ht, ?_⟩
  change Subtype.val ⁻¹' hull F (kernel F (Subtype.val '' t)) =
    Subtype.val ⁻¹' hull F (kernel F (Subtype.val '' s))
  rw [hk t, hk s, heq]

/-- The exact finite-character equation for the same relative closure. -/
theorem subspace_closure_eq_iUnion_finite
    (F : Set (Set V)) (hF : Set.univ ∉ F) (G : Set F)
    (P : G → Submodule 𝕜 V) (hP : ∀ I : G, (P I : Set V) = I.val.val) :
    ∀ s : Set G, ((space F hF).subspace G).closure s =
      ⋃ (t : Set G) (_ : t ⊆ s) (_ : t.Finite), ((space F hF).subspace G).closure t :=
  ClosureSpace.closure_eq_iUnion_finite_of_exists_finite_subset _
    (exists_finite_subset_subspace_closure_eq F hF G P hP)

end ClosureSpace.HullKernel
