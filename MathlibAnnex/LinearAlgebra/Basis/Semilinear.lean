/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Semilinear equivalences determined by two bases

The scalar ring isomorphism and bases determine the map on every finitely
supported coordinate family. The basis index may be infinite. These declarations
were extracted from the projectivization construction without changing their
mathematical hypotheses or proofs; no projective incidence is needed here.
-/

set_option autoImplicit false
noncomputable section

namespace Module.Basis

universe uK uL uV uW uI
variable {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
variable [Field K] [Field L]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
variable {ι : Type uI}

local instance (σ : K ≃+* L) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : K ≃+* L) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- The semilinear equivalence determined by a scalar isomorphism and two
arbitrary bases. Coefficients are finitely supported; the index type need not
be finite. This construction alone does not assert agreement with a point map. -/
def semilinearEquiv (b : Module.Basis ι K V) (c : Module.Basis ι L W)
    (σ : K ≃+* L) : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) V W where
  toFun v := c.repr.symm (Finsupp.mapRange σ σ.map_zero (b.repr v))
  invFun w := b.repr.symm (Finsupp.mapRange σ.symm σ.symm.map_zero (c.repr w))
  left_inv v := by
    apply b.repr.injective
    ext i
    simp
  right_inv w := by
    apply c.repr.injective
    ext i
    simp
  map_add' v w := by
    apply c.repr.injective
    ext i
    simp
  map_smul' a v := by
    apply c.repr.injective
    ext i
    simp [map_mul]

/-- Every coefficient of the actual semilinear map is prescribed. -/
@[simp]
theorem repr_semilinearEquiv (b : Module.Basis ι K V) (c : Module.Basis ι L W)
    (σ : K ≃+* L) (v : V) (i : ι) :
    c.repr (semilinearEquiv b c σ v) i = σ (b.repr v i) := by
  change c.repr (c.repr.symm (Finsupp.mapRange σ σ.map_zero (b.repr v))) i = _
  simp

/-- The inverse has coefficient map `σ.symm`, with no choice of lifts. -/
@[simp]
theorem repr_semilinearEquiv_symm (b : Module.Basis ι K V)
    (c : Module.Basis ι L W) (σ : K ≃+* L) (w : W) (i : ι) :
    b.repr ((semilinearEquiv b c σ).symm w) i = σ.symm (c.repr w i) := by
  change b.repr (b.repr.symm (Finsupp.mapRange σ.symm σ.symm.map_zero (c.repr w))) i = _
  simp

/-- Evaluation on each basis vector. -/
@[simp]
theorem semilinearEquiv_apply_basis (b : Module.Basis ι K V)
    (c : Module.Basis ι L W) (σ : K ≃+* L) (i : ι) :
    semilinearEquiv b c σ (b i) = c i := by
  classical
  apply c.repr.injective
  ext j
  change c.repr (semilinearEquiv b c σ (b i)) j = c.repr (c i) j
  rw [repr_semilinearEquiv]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- Evaluation on every finite linear combination, not just the basis rays. -/
theorem semilinearEquiv_sum (b : Module.Basis ι K V)
    (c : Module.Basis ι L W) (σ : K ≃+* L) (s : Finset ι) (a : ι → K) :
    semilinearEquiv b c σ (∑ i ∈ s, a i • b i) =
      ∑ i ∈ s, σ (a i) • c i := by
  simp only [map_sum, map_smulₛₗ, semilinearEquiv_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end Module.Basis
