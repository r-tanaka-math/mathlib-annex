/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CStarRealization

/-!
# Testing finite conjugation on actual C-star geometric structure spaces

The algebra witness universe and the target universe are independent. Tests on
all actual C-star algebras of a fixed universe imply the class-relative property
for realizable source carriers in ANY universe. For the converse, a carrier
universe containing the algebra universe is sufficient: the proof below uses
an actual `ULift` of each geometric structure space and its induced closure.
There is no unsupported shrinking of a large witness into a smaller universe.

Only forward full continuity of the two finite homeomorphisms is assumed.
Neither an elementary-algebra characterization nor an operator-ideal assertion
is a consequence of these changes of test coordinates alone.
-/

@[expose] public section

set_option autoImplicit false

namespace ClosureSpace

/-- Test every component of every actual nontrivial complex C-star algebra in
`Type uA`. The test inputs are the existing finite homeomorphisms, with forward
full continuity only. This is a specialization of the test family, not a new
notion of finite homeomorphism or a certificate asserting the characterization. -/
def HasCStarComponentFiniteConjugation.{uA, uX} {X : Type uX}
    (c : ClosureSpace X) : Prop :=
  ∀ (A : Type uA) [NonUnitalCStarAlgebra A] [Nontrivial A],
    ∀ I : NormedSpace.GeometricStructureSpace ℂ A,
      ∀ f : FiniteHomeomorph
          ((NormedSpace.geometricStructureClosure ℂ A).subspace
            ((NormedSpace.geometricStructureClosure ℂ A).component I)) c,
        ((NormedSpace.geometricStructureClosure ℂ A).subspace
          ((NormedSpace.geometricStructureClosure ℂ A).component I)).Continuous c f.toEquiv →
        ∀ g : FiniteHomeomorph
            ((NormedSpace.geometricStructureClosure ℂ A).subspace
              ((NormedSpace.geometricStructureClosure ℂ A).component I))
            ((NormedSpace.geometricStructureClosure ℂ A).subspace
              ((NormedSpace.geometricStructureClosure ℂ A).component I)),
          ((NormedSpace.geometricStructureClosure ℂ A).subspace
            ((NormedSpace.geometricStructureClosure ℂ A).component I)).Continuous
              ((NormedSpace.geometricStructureClosure ℂ A).subspace
                ((NormedSpace.geometricStructureClosure ℂ A).component I)) g.toEquiv →
          c.Continuous c (f.conjugate g).toEquiv ∧
            c.Continuous c (f.conjugate g).toEquiv.symm

universe uA uL uX
variable {X : Type uX} {c : ClosureSpace X}

/-- Extract the actual algebra witness of any realizable source, restrict its
homeomorphism to the actual component, and reparameterize both test maps. -/
theorem HasCStarComponentFiniteConjugation.hasContinuousFiniteConjugation
    (hc : HasCStarComponentFiniteConjugation.{uA, uX} c) :
    c.HasContinuousFiniteConjugation (ClosureCat.IsCStarRealizable.{uA, uL}) := by
  intro L hL t f hf g hg
  obtain ⟨A, instA, hA, ⟨a⟩⟩ := hL
  letI : NonUnitalCStarAlgebra A := instA
  letI : Nontrivial A := hA
  let d := NormedSpace.geometricStructureClosure ℂ A
  let I := a.toEquiv.symm t
  let b : Homeomorph (d.subspace (d.component I))
      (L.str.subspace (L.str.component t)) := by
    have hb := a.component (a.toEquiv.symm t)
    change Homeomorph (d.subspace (d.component (a.toEquiv.symm t)))
      (L.str.subspace (L.str.component (a.toEquiv (a.toEquiv.symm t)))) at hb
    rw [a.toEquiv.apply_symm_apply] at hb
    exact hb
  let f' := b.toFiniteHomeomorph.trans f
  let g' := b.symm.toFiniteHomeomorph.conjugate g
  have hf' : (d.subspace (d.component I)).Continuous c f'.toEquiv :=
    hf.comp b.continuous_toFun
  have hg' : (d.subspace (d.component I)).Continuous
      (d.subspace (d.component I)) g'.toEquiv :=
    b.continuous_invFun.comp (hg.comp b.continuous_toFun)
  have hh := hc A I f' hf' g' hg'
  have heq : (f'.conjugate g').toEquiv = (f.conjugate g).toEquiv :=
    FiniteHomeomorph.conjugate_reparam_toEquiv b f g
  rw [heq] at hh
  exact hh

/-- At the algebra carrier universe, the converse uses the actual GSS itself
as an eligible source. Nontriviality belongs to the witness, not to the target. -/
theorem hasContinuousFiniteConjugation_iff_cstar_components :
    c.HasContinuousFiniteConjugation (ClosureCat.IsCStarRealizable.{uA, uA}) ↔
      HasCStarComponentFiniteConjugation.{uA, uX} c := by
  constructor
  · intro hc A instA hA I f hf g hg
    exact hc (ClosureCat.of (NormedSpace.GeometricStructureSpace ℂ A)
      (NormedSpace.geometricStructureClosure ℂ A))
      (ClosureCat.isCStarRealizable_geometricStructureSpace A) I f hf g hg
  · exact HasCStarComponentFiniteConjugation.hasContinuousFiniteConjugation

/-- In any carrier universe of the form `max uA uL`, lift each actual GSS
upwards. The inverse direction never compresses a larger algebra or GSS. -/
theorem hasContinuousFiniteConjugation_iff_cstar_components_max :
    c.HasContinuousFiniteConjugation
        (ClosureCat.IsCStarRealizable.{uA, max uA uL}) ↔
      HasCStarComponentFiniteConjugation.{uA, uX} c := by
  constructor
  · intro hc A instA hA I f hf g hg
    let d := NormedSpace.geometricStructureClosure ℂ A
    let p : ULift.{uL} (NormedSpace.GeometricStructureSpace ℂ A) ≃
        NormedSpace.GeometricStructureSpace ℂ A := Equiv.ulift
    let L : ClosureCat.{max uA uL} :=
      ClosureCat.of (ULift.{uL} (NormedSpace.GeometricStructureSpace ℂ A)) (d.induced p)
    let a : Homeomorph L.str d := homeomorphInduced d p
    have hL : ClosureCat.IsCStarRealizable.{uA, max uA uL} L :=
      ⟨A, instA, hA, ⟨a.symm⟩⟩
    let b : Homeomorph (L.str.subspace (L.str.component (ULift.up I)))
        (d.subspace (d.component I)) := a.component (ULift.up I)
    let f' := b.toFiniteHomeomorph.trans f
    let g' := b.symm.toFiniteHomeomorph.conjugate g
    have hf' : (L.str.subspace (L.str.component (ULift.up I))).Continuous c f'.toEquiv :=
      hf.comp b.continuous_toFun
    have hg' : (L.str.subspace (L.str.component (ULift.up I))).Continuous
        (L.str.subspace (L.str.component (ULift.up I))) g'.toEquiv :=
      b.continuous_invFun.comp (hg.comp b.continuous_toFun)
    have hh := hc L hL (ULift.up I) f' hf' g' hg'
    have heq : (f'.conjugate g').toEquiv = (f.conjugate g).toEquiv :=
      FiniteHomeomorph.conjugate_reparam_toEquiv b f g
    rw [heq] at hh
    exact hh
  · exact HasCStarComponentFiniteConjugation.hasContinuousFiniteConjugation

/-- The actual-algebra test family is invariant under full target
homeomorphisms, with no inverse-continuity requirement on the test inputs. -/
theorem Homeomorph.hasCStarComponentFiniteConjugation_iff
    {Y : Type uL} {d : ClosureSpace Y} (a : Homeomorph c d) :
    HasCStarComponentFiniteConjugation.{uA, uX} c ↔
      HasCStarComponentFiniteConjugation.{uA, uL} d := by
  rw [← hasContinuousFiniteConjugation_iff_cstar_components,
    ← hasContinuousFiniteConjugation_iff_cstar_components]
  exact a.hasContinuousFiniteConjugation_iff

end ClosureSpace
