import MathlibAnnex.Analysis.CStarAlgebra.Cyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.NonUnital
import MathlibAnnex.Analysis.CStarAlgebra.Representation

/-!
# Adapters between the representation interfaces

The project inherited two representation APIs.  This file proves their exact
relationship, including the nonzero condition deliberately present in
`Representation.IsIrreducible` and absent from `StarAlgHom.IsIrreducible`.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace Representation

/-- The two inherited unitary-equivalence predicates are definitionally the
same mathematical statement. -/
theorem unitaryEquivalent_iff_starAlgHom
    (pi : Representation A H) (rho : Representation A K) :
    pi.UnitaryEquivalent rho ↔ StarAlgHom.UnitaryEquivalent pi rho :=
  Iff.rfl

/-- A nonzero represented operator forces the Hilbert space to be nontrivial. -/
theorem nontrivial_of_isNonzero (pi : Representation A H) (hpi : pi.IsNonzero) :
    Nontrivial H := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  obtain ⟨a, ha⟩ := hpi
  exact ha (Subsingleton.elim (pi a) 0)

/-- The reducing predicates agree once the separate closedness field is made
explicit. -/
theorem reduces_iff_closed_and_isReducing (pi : Representation A H)
    (L : Submodule ℂ H) :
    pi.Reduces L ↔ IsClosed (L : Set H) ∧ StarAlgHom.IsReducing pi L := by
  constructor
  · intro h
    refine ⟨h.1, fun a ↦ ⟨?_, ?_⟩⟩
    · intro x hx
      exact (h.2 a x hx).1
    · intro x hx
      exact (h.2 a x hx).2
  · rintro ⟨hclosed, hreduces⟩
    refine ⟨hclosed, ?_⟩
    intro a x hx
    exact ⟨(hreduces a).1 hx, (hreduces a).2 hx⟩

/-- Nonzero irreducibility implies the closed-reducing-subspace predicate used
by the Schur and cyclic-transport modules. -/
theorem isIrreducible_starAlgHom (pi : Representation A H)
    (hirr : pi.IsIrreducible) : StarAlgHom.IsIrreducible pi := by
  intro L hclosed hreduces
  exact hirr.2 L ((reduces_iff_closed_and_isReducing pi L).2 ⟨hclosed, hreduces⟩)

/-- On a nontrivial Hilbert space, the closed-reducing-subspace predicate and
the project's explicitly nonzero irreducibility predicate are equivalent. -/
theorem isIrreducible_iff_starAlgHom [Nontrivial H]
    (pi : Representation A H) :
    pi.IsIrreducible ↔ StarAlgHom.IsIrreducible pi := by
  constructor
  · exact isIrreducible_starAlgHom pi
  · intro hirr
    refine ⟨pi.isNonzero_of_nontrivial, ?_⟩
    intro L hreduces
    exact hirr L hreduces.1
      ((reduces_iff_closed_and_isReducing pi L).1 hreduces).2

/-- Every nonzero vector has dense represented orbit in the explicitly
nonzero irreducible interface.  This is the concrete bridge between the two
inherited cyclic-subspace definitions. -/
theorem denseRange_orbitMap_of_isIrreducible (pi : Representation A H)
    (hirr : pi.IsIrreducible) {xi : H} (hxi : xi ≠ 0) :
    DenseRange (StarAlgHom.orbitMap pi xi) := by
  have htop : StarAlgHom.cyclicSubspace pi xi = ⊤ :=
    StarAlgHom.cyclicSubspace_eq_top pi (isIrreducible_starAlgHom pi hirr) hxi
  have hsets := congrArg (fun L : Submodule ℂ H ↦ (L : Set H)) htop
  rw [denseRange_iff_closure_range]
  simpa [StarAlgHom.cyclicSubspace, StarAlgHom.orbitMap,
    Submodule.topologicalClosure_coe, LinearMap.coe_range] using hsets

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
