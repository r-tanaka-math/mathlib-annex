/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.Maps

/-!
# Finite homeomorphism composition and conjugation

The composition, conjugate and source-reparameterization identities depend only
on closure-space maps, not on categories or a class-relative property.
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

namespace ClosureSpace

variable {α : Type u} {β : Type v} {γ : Type w}
variable {c : ClosureSpace α} {d : ClosureSpace β} {k : ClosureSpace γ}

/-- Compose the existing finite homeomorphisms; `f.trans g` acts as `g ∘ f`. -/
def FiniteHomeomorph.trans (f : FiniteHomeomorph c d) (g : FiniteHomeomorph d k) :
    FiniteHomeomorph c k where
  toEquiv := f.toEquiv.trans g.toEquiv
  finitelyContinuous_toFun := g.finitelyContinuous_toFun.comp f.finitelyContinuous_toFun
  finitelyContinuous_invFun := f.finitelyContinuous_invFun.comp g.finitelyContinuous_invFun

@[simp]
theorem FiniteHomeomorph.trans_apply (f : FiniteHomeomorph c d)
    (g : FiniteHomeomorph d k) (x : α) :
    (f.trans g).toEquiv x = g.toEquiv (f.toEquiv x) := rfl

@[simp]
theorem FiniteHomeomorph.trans_symm_apply (f : FiniteHomeomorph c d)
    (g : FiniteHomeomorph d k) (z : γ) :
    (f.trans g).toEquiv.symm z = f.toEquiv.symm (g.toEquiv.symm z) := rfl

/-- Conjugation on the target. Full continuity is not part of this construction. -/
def FiniteHomeomorph.conjugate (f : FiniteHomeomorph c d)
    (g : FiniteHomeomorph c c) : FiniteHomeomorph d d :=
  f.symm.trans (g.trans f)

@[simp]
theorem FiniteHomeomorph.conjugate_apply (f : FiniteHomeomorph c d)
    (g : FiniteHomeomorph c c) (y : β) :
    (f.conjugate g).toEquiv y = f.toEquiv (g.toEquiv (f.toEquiv.symm y)) := rfl

@[simp]
theorem FiniteHomeomorph.conjugate_symm_apply (f : FiniteHomeomorph c d)
    (g : FiniteHomeomorph c c) (y : β) :
    (f.conjugate g).toEquiv.symm y =
      f.toEquiv (g.toEquiv.symm (f.toEquiv.symm y)) := rfl

/-- Changing source coordinates by a full homeomorphism leaves the conjugate
unchanged as an actual equivalence, including its inverse. -/
theorem FiniteHomeomorph.conjugate_reparam_toEquiv (a : Homeomorph c d)
    (f : FiniteHomeomorph d k) (g : FiniteHomeomorph d d) :
    ((a.toFiniteHomeomorph.trans f).conjugate
      (a.symm.toFiniteHomeomorph.conjugate g)).toEquiv =
      (f.conjugate g).toEquiv := by
  apply Equiv.ext
  intro z
  change f.toEquiv (a.toEquiv (a.toEquiv.symm
    (g.toEquiv (a.toEquiv (a.toEquiv.symm (f.toEquiv.symm z)))))) =
      f.toEquiv (g.toEquiv (f.toEquiv.symm z))
  simp only [Equiv.apply_symm_apply]

/-- The same coordinate change transports full continuity of the conjugate
in both directions. It assumes no continuity of the inverses of `f` or `g`. -/
theorem FiniteHomeomorph.continuous_conjugate_reparam_iff (a : Homeomorph c d)
    (f : FiniteHomeomorph d k) (g : FiniteHomeomorph d d) :
    (k.Continuous k ((a.toFiniteHomeomorph.trans f).conjugate
        (a.symm.toFiniteHomeomorph.conjugate g)).toEquiv ∧
      k.Continuous k ((a.toFiniteHomeomorph.trans f).conjugate
        (a.symm.toFiniteHomeomorph.conjugate g)).toEquiv.symm) ↔
    (k.Continuous k (f.conjugate g).toEquiv ∧
      k.Continuous k (f.conjugate g).toEquiv.symm) := by
  rw [FiniteHomeomorph.conjugate_reparam_toEquiv]

end ClosureSpace
