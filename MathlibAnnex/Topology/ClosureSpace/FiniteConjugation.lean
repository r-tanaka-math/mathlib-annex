/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.FiniteHomeomorph
public import MathlibAnnex.Topology.ClosureSpace.Category
public import MathlibAnnex.Topology.ClosureSpace.ComponentSubspace

/-!
# Continuous conjugation of finite homeomorphisms

For a class `D : ClosureCat → Prop`, `HasContinuousFiniteConjugation c D`
quantifies over every eligible source object and every one of its components,
with the existing subspace closure. The two inputs are finite homeomorphisms
whose FORWARD functions are fully continuous. Their inverses are not assumed
fully continuous. The conclusion concerns both directions of the actual
conjugate `f ∘ g ∘ f⁻¹`.

This is the closure-language property occurring in Theorem 7.7(ii) of
arXiv:2504.05551v1, not a definition of an elementary algebra and not a proof
of that characterization. Target and eligible-source carrier universes are
independent. No ordinary topology or closedness of a component is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

namespace ClosureSpace

variable {α : Type u} {β : Type v} {γ : Type w}
variable {c : ClosureSpace α} {d : ClosureSpace β} {k : ClosureSpace γ}

/-- Relative finite-conjugation property. The source class is not restricted
to a chosen object or algebra. Components retain their actual subspace closure. -/
def HasContinuousFiniteConjugation (c : ClosureSpace α) (D : ClosureCat.{s} → Prop) : Prop :=
  ∀ (L : ClosureCat.{s}), D L → ∀ t : L,
    ∀ f : FiniteHomeomorph (L.str.subspace (L.str.component t)) c,
      (L.str.subspace (L.str.component t)).Continuous c f.toEquiv →
      ∀ g : FiniteHomeomorph (L.str.subspace (L.str.component t))
          (L.str.subspace (L.str.component t)),
        (L.str.subspace (L.str.component t)).Continuous
          (L.str.subspace (L.str.component t)) g.toEquiv →
        c.Continuous c (f.conjugate g).toEquiv ∧
          c.Continuous c (f.conjugate g).toEquiv.symm

/-- The property gives a full homeomorphism with exactly the prescribed
conjugate equivalence; this is a construction from the defined property. -/
def HasContinuousFiniteConjugation.conjugateHomeomorph
    {D : ClosureCat.{s} → Prop} (hc : c.HasContinuousFiniteConjugation D)
    (L : ClosureCat.{s}) (hL : D L) (t : L)
    (f : FiniteHomeomorph (L.str.subspace (L.str.component t)) c)
    (hf : (L.str.subspace (L.str.component t)).Continuous c f.toEquiv)
    (g : FiniteHomeomorph (L.str.subspace (L.str.component t))
      (L.str.subspace (L.str.component t)))
    (hg : (L.str.subspace (L.str.component t)).Continuous
      (L.str.subspace (L.str.component t)) g.toEquiv) : Homeomorph c c where
  toEquiv := (f.conjugate g).toEquiv
  continuous_toFun := (hc L hL t f hf g hg).1
  continuous_invFun := (hc L hL t f hf g hg).2

@[simp]
theorem HasContinuousFiniteConjugation.conjugateHomeomorph_apply
    {D : ClosureCat.{s} → Prop} (hc : c.HasContinuousFiniteConjugation D)
    (L : ClosureCat.{s}) (hL : D L) (t : L)
    (f : FiniteHomeomorph (L.str.subspace (L.str.component t)) c)
    (hf : (L.str.subspace (L.str.component t)).Continuous c f.toEquiv)
    (g : FiniteHomeomorph (L.str.subspace (L.str.component t))
      (L.str.subspace (L.str.component t)))
    (hg : (L.str.subspace (L.str.component t)).Continuous
      (L.str.subspace (L.str.component t)) g.toEquiv) (x : α) :
    (hc.conjugateHomeomorph L hL t f hf g hg).toEquiv x =
      f.toEquiv (g.toEquiv (f.toEquiv.symm x)) := rfl

@[simp]
theorem HasContinuousFiniteConjugation.conjugateHomeomorph_symm_apply
    {D : ClosureCat.{s} → Prop} (hc : c.HasContinuousFiniteConjugation D)
    (L : ClosureCat.{s}) (hL : D L) (t : L)
    (f : FiniteHomeomorph (L.str.subspace (L.str.component t)) c)
    (hf : (L.str.subspace (L.str.component t)).Continuous c f.toEquiv)
    (g : FiniteHomeomorph (L.str.subspace (L.str.component t))
      (L.str.subspace (L.str.component t)))
    (hg : (L.str.subspace (L.str.component t)).Continuous
      (L.str.subspace (L.str.component t)) g.toEquiv) (x : α) :
    (hc.conjugateHomeomorph L hL t f hf g hg).toEquiv.symm x =
      f.toEquiv (g.toEquiv.symm (f.toEquiv.symm x)) := rfl

/-- Restrict the eligible class, retaining its full quantification. -/
theorem HasContinuousFiniteConjugation.mono {D E : ClosureCat.{s} → Prop}
    (hc : c.HasContinuousFiniteConjugation D) (hED : ∀ L, E L → D L) :
    c.HasContinuousFiniteConjugation E :=
  fun L hL t f hf g hg => hc L (hED L hL) t f hf g hg

/-- A full target homeomorphism preserves the property. No full inverse
continuity is added to the two finite-homeomorphism inputs. -/
theorem Homeomorph.hasContinuousFiniteConjugation {D : ClosureCat.{s} → Prop}
    (a : Homeomorph c d) (hc : c.HasContinuousFiniteConjugation D) :
    d.HasContinuousFiniteConjugation D := by
  intro L hL t f hf g hg
  let f' := f.trans a.symm.toFiniteHomeomorph
  have hf' : (L.str.subspace (L.str.component t)).Continuous c f'.toEquiv :=
    a.continuous_invFun.comp hf
  let b := hc.conjugateHomeomorph L hL t f' hf' g hg
  let q : Homeomorph d d := a.symm.trans (b.trans a)
  have hq : q.toEquiv = (f.conjugate g).toEquiv := by
    apply Equiv.ext
    intro y
    change a.toEquiv (a.toEquiv.symm
      (f.toEquiv (g.toEquiv (f.toEquiv.symm (a.toEquiv (a.toEquiv.symm y)))))) =
        f.toEquiv (g.toEquiv (f.toEquiv.symm y))
    simp only [Equiv.apply_symm_apply]
  constructor
  · rw [← hq]
    exact q.continuous_toFun
  · rw [← hq]
    exact q.continuous_invFun

/-- Target homeomorphism invariance, in both directions. -/
theorem Homeomorph.hasContinuousFiniteConjugation_iff {D : ClosureCat.{s} → Prop}
    (a : Homeomorph c d) :
    c.HasContinuousFiniteConjugation D ↔ d.HasContinuousFiniteConjugation D :=
  ⟨a.hasContinuousFiniteConjugation, a.symm.hasContinuousFiniteConjugation⟩

/-- Enlarge the eligible class by genuine homeomorphic copies. Source carrier
universes may differ. Every new object is supplied with an actual old witness;
we pull back its distinguished point and restrict the witness to that component. -/
theorem HasContinuousFiniteConjugation.of_source_homeomorphs
    {D : ClosureCat.{s} → Prop} {E : ClosureCat.{t} → Prop}
    (hc : c.HasContinuousFiniteConjugation D)
    (hED : ∀ (M : ClosureCat.{t}), E M →
      ∃ L : ClosureCat.{s}, D L ∧ Nonempty (Homeomorph L.str M.str)) :
    c.HasContinuousFiniteConjugation E := by
  intro M hM x f hf g hg
  obtain ⟨L, hL, ⟨a⟩⟩ := hED M hM
  let y := a.toEquiv.symm x
  let b : Homeomorph (L.str.subspace (L.str.component y))
      (M.str.subspace (M.str.component x)) := by
    have hb := a.component y
    change Homeomorph (L.str.subspace (L.str.component y))
      (M.str.subspace (M.str.component (a.toEquiv y))) at hb
    have hxy : a.toEquiv y = x := a.toEquiv.apply_symm_apply x
    rw [hxy] at hb
    exact hb
  let f' := b.toFiniteHomeomorph.trans f
  let g' := b.symm.toFiniteHomeomorph.conjugate g
  have hf' : (L.str.subspace (L.str.component y)).Continuous c f'.toEquiv :=
    hf.comp b.continuous_toFun
  have hg' : (L.str.subspace (L.str.component y)).Continuous
      (L.str.subspace (L.str.component y)) g'.toEquiv :=
    b.continuous_invFun.comp (hg.comp b.continuous_toFun)
  have hh := hc L hL y f' hf' g' hg'
  have heq : (f'.conjugate g').toEquiv = (f.conjugate g).toEquiv :=
    FiniteHomeomorph.conjugate_reparam_toEquiv b f g
  rw [heq] at hh
  exact hh

/-- Equivalent choices of source coordinates give the same target property. -/
theorem hasContinuousFiniteConjugation_iff_of_source_homeomorphs
    {D : ClosureCat.{s} → Prop} {E : ClosureCat.{t} → Prop}
    (hED : ∀ (M : ClosureCat.{t}), E M →
      ∃ L : ClosureCat.{s}, D L ∧ Nonempty (Homeomorph L.str M.str))
    (hDE : ∀ (L : ClosureCat.{s}), D L →
      ∃ M : ClosureCat.{t}, E M ∧ Nonempty (Homeomorph M.str L.str)) :
    c.HasContinuousFiniteConjugation D ↔ c.HasContinuousFiniteConjugation E :=
  ⟨fun hc => hc.of_source_homeomorphs hED, fun hc => hc.of_source_homeomorphs hDE⟩

/-- Reparameterize a target component using its existing restriction homeomorphism. -/
theorem Homeomorph.hasContinuousFiniteConjugation_component_iff
    {D : ClosureCat.{s} → Prop} (a : Homeomorph c d) (x : α) :
    (c.subspace (c.component x)).HasContinuousFiniteConjugation D ↔
      (d.subspace (d.component (a.toEquiv x))).HasContinuousFiniteConjugation D :=
  (a.component x).hasContinuousFiniteConjugation_iff

/-- The existential component condition in 7.7(ii) is invariant under a full
ambient homeomorphism. This does not assert that any space satisfies it. -/
theorem Homeomorph.exists_hasContinuousFiniteConjugation_component_iff
    {D : ClosureCat.{s} → Prop} (a : Homeomorph c d) :
    (∃ x : α, (c.subspace (c.component x)).HasContinuousFiniteConjugation D) ↔
      ∃ y : β, (d.subspace (d.component y)).HasContinuousFiniteConjugation D := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨a.toEquiv x, (a.hasContinuousFiniteConjugation_component_iff x).mp hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨a.toEquiv.symm y, ?_⟩
    apply (a.hasContinuousFiniteConjugation_component_iff (a.toEquiv.symm y)).mpr
    change (d.subspace (d.component (a.toEquiv (a.toEquiv.symm y)))).HasContinuousFiniteConjugation D
    rw [a.toEquiv.apply_symm_apply]
    exact hy

end ClosureSpace
