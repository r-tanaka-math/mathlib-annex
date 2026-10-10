/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import MathlibAnnex.Analysis.Normed.GeometricStructure.Basic
public import MathlibAnnex.Topology.ClosureSpace.FiniteConjugation

/-!
# Closure spaces realized by nontrivial complex C-star algebras

`ClosureCat.IsCStarRealizable.{uA,uX} X` uses an actual algebra of carrier
universe `uA`, its actual nonunital C-star algebra structure, a nontriviality
proof and an actual homeomorphism from its face-defined geometric structure
space to `X`. The carrier of `X` has the independent universe `uX`.

This is the object predicate in Definition 7.4 of arXiv:2504.05551v1. It is
homeomorphism-closed, including across carrier universes, and hence invariant
under the existing categorical isomorphisms. No categorical wrapper is needed
for the class-relative property: use
`c.HasContinuousFiniteConjugation (ClosureCat.IsCStarRealizable.{uA,uX})`.
That expression quantifies over ALL eligible objects of the indicated carrier
universe and ALL their component points, not over one selected algebra.

No separability, unitality, order structure, choice of irreducible representation,
or assertion of the characterization of elementary algebras is part of the
witness. The pre-existing geometric structure space definition is unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace ClosureCat

/-- An actual nontrivial complex C-star algebra realization of a closure space.
The algebra's universe and the target carrier's universe are explicit and independent. -/
def IsCStarRealizable.{uA, uX} (X : ClosureCat.{uX}) : Prop :=
  ∃ (A : Type uA) (instA : NonUnitalCStarAlgebra A),
    letI : NonUnitalCStarAlgebra A := instA
    Nontrivial A ∧ Nonempty
      (ClosureSpace.Homeomorph (NormedSpace.geometricStructureClosure ℂ A) X.str)

universe uA uX uY

/-- Every nontrivial complex C-star algebra realizes its actual face-defined GSS. -/
theorem isCStarRealizable_geometricStructureSpace (A : Type uA)
    [NonUnitalCStarAlgebra A] [Nontrivial A] :
    IsCStarRealizable.{uA, uA}
      (ClosureCat.of (NormedSpace.GeometricStructureSpace ℂ A)
        (NormedSpace.geometricStructureClosure ℂ A)) :=
  ⟨A, inferInstance, inferInstance, ⟨ClosureSpace.Homeomorph.refl _⟩⟩

/-- Transport the same witness algebra and its homeomorphism; there is no
new representation or replacement of the original geometric structure space. -/
theorem IsCStarRealizable.homeomorph {X : ClosureCat.{uX}} {Y : ClosureCat.{uY}}
    (hX : IsCStarRealizable.{uA, uX} X) (e : ClosureSpace.Homeomorph X.str Y.str) :
    IsCStarRealizable.{uA, uY} Y := by
  rcases hX with ⟨A, instA, hA, ⟨f⟩⟩
  letI : NonUnitalCStarAlgebra A := instA
  exact ⟨A, instA, hA, ⟨f.trans e⟩⟩

/-- Homeomorphism-closedness in both directions, keeping the witness universe. -/
theorem isCStarRealizable_iff_of_homeomorph {X : ClosureCat.{uX}} {Y : ClosureCat.{uY}}
    (e : ClosureSpace.Homeomorph X.str Y.str) :
    IsCStarRealizable.{uA, uX} X ↔ IsCStarRealizable.{uA, uY} Y :=
  ⟨fun hX => hX.homeomorph e, fun hY => hY.homeomorph e.symm⟩

/-- The object predicate is isomorphism-closed in the existing category of
closure spaces with fully continuous arrows. -/
theorem isCStarRealizable_iff_of_iso {X Y : ClosureCat.{uX}}
    (e : CategoryTheory.Iso X Y) :
    IsCStarRealizable.{uA, uX} X ↔ IsCStarRealizable.{uA, uX} Y :=
  isCStarRealizable_iff_of_homeomorph (ClosureCat.homeomorphOfIso e)

end ClosureCat
