/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic

/-!
# Cardinality of Hilbert bases under continuous semilinear equivalences

These statements compare the indices of actual Hilbert bases, not Hamel ranks
or the cardinality of the ambient vector spaces. All four type universes are
independent. A scalar ring automorphism is permitted in the core result; only
the vector-space map and its inverse are required to be continuous.

For each image basis vector the coordinate support is countable. The supports
cover the target index, by the actual convergent Hilbert expansion. This yields
an injection into the source index times the natural numbers. Infinite indices
absorb the countable factor. A finite index is treated separately using the
finite algebraic basis supplied by `HilbertBasis.toOrthonormalBasis`.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped BigOperators Cardinal

namespace HilbertBasis

universe uI uJ uH uK uF
variable {𝕜 : Type uF} [RCLike 𝕜]
variable {ι : Type uI} {κ : Type uJ}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

local instance (σ : 𝕜 ≃+* 𝕜) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : 𝕜 ≃+* 𝕜) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- Each vector has countably many nonzero Hilbert coordinates, regardless of
whether the Hilbert space itself is separable. -/
theorem countable_support_repr (b : HilbertBasis ι 𝕜 H) (x : H) :
    (Function.support (fun i => b.repr x i)).Countable := by
  apply (b.hasSum_repr x).summable.countable_support.mono
  intro i hi
  change b.repr x i • b i ≠ 0
  exact smul_ne_zero hi (b.orthonormal.linearIndependent.ne_zero i)

/-- A continuous semilinear functional is determined by its values on a Hilbert
basis. The density used here is proved upstream from `hasSum_repr`. -/
theorem semilinear_map_eq_zero_of_apply_eq_zero (b : HilbertBasis ι 𝕜 H)
    {σ : 𝕜 →+* 𝕜} (f : H →ₛₗ[σ] 𝕜) (hf : Continuous f)
    (hzero : ∀ i, f (b i) = 0) : f = 0 := by
  have hspan : Submodule.span 𝕜 (Set.range b) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hzero i
  have hc : IsClosed (f.ker : Set H) := by
    change IsClosed {x : H | f x = 0}
    exact isClosed_eq hf continuous_const
  have ht : (Submodule.span 𝕜 (Set.range b)).topologicalClosure ≤ f.ker :=
    Submodule.topologicalClosure_minimal _ hspan hc
  rw [b.dense_span] at ht
  ext x
  exact ht (Submodule.mem_top : x ∈ (⊤ : Submodule 𝕜 H))

/-- Every target coordinate occurs in an image basis vector. This uses
continuity and surjectivity of the actual semilinear map, not algebraic
spanning by an infinite Hilbert basis. -/
theorem exists_repr_apply_ne_zero_of_surjective
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    {σ : 𝕜 →+* 𝕜} (f : H →ₛₗ[σ] K)
    (hf : Continuous f) (hsurj : Function.Surjective f) (j : κ) :
    ∃ i, c.repr (f (b i)) j ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let L : H →ₛₗ[σ] 𝕜 :=
    { toFun := fun x => inner 𝕜 (c j) (f x)
      map_add' := by intros; simp only [map_add, inner_add_right]
      map_smul' := by
        intros
        simp only [map_smulₛₗ, inner_smul_right, smul_eq_mul] }
  have hL : Continuous L := continuous_const.inner hf
  have hz : L = 0 := b.semilinear_map_eq_zero_of_apply_eq_zero L hL (by
    intro i
    change inner 𝕜 (c j) (f (b i)) = 0
    simpa only [HilbertBasis.repr_apply_apply] using h i)
  obtain ⟨x, hx⟩ := hsurj (c j)
  have hself : inner 𝕜 (c j) (c j) = 0 := by
    have hval := congrArg (fun g : H →ₛₗ[σ] 𝕜 => g x) hz
    change inner 𝕜 (c j) (f x) = 0 at hval
    simpa only [hx] using hval
  exact c.orthonormal.linearIndependent.ne_zero j (inner_self_eq_zero.mp hself)

/-- Countable coordinate supports give an actual injection into `ι × ℕ`.
Empty indices are allowed: the surjectivity/density argument handles them. -/
theorem nonempty_embedding_prod_nat_of_surjective
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    {σ : 𝕜 →+* 𝕜} (f : H →ₛₗ[σ] K)
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    Nonempty (κ ↪ ι × ℕ) := by
  classical
  let S : ι → Set κ := fun i => Function.support (fun j => c.repr (f (b i)) j)
  have hcount : ∀ i, (S i).Countable := fun i => c.countable_support_repr (f (b i))
  have hcode : ∀ i, ∃ a : S i → ℕ, Function.Injective a := by
    intro i
    letI : Countable (S i) := (hcount i).to_subtype
    exact Countable.exists_injective_nat (S i)
  choose code hcode using hcode
  have hcover : ∀ j : κ, ∃ i, j ∈ S i :=
    b.exists_repr_apply_ne_zero_of_surjective c f hf hsurj
  choose pick hpick using hcover
  refine ⟨⟨fun j => (pick j, code (pick j) ⟨j, hpick j⟩), ?_⟩⟩
  intro j k heq
  have hfst : pick j = pick k := congrArg Prod.fst heq
  have hsnd := congrArg Prod.snd heq
  change code (pick j) ⟨j, hpick j⟩ = code (pick k) ⟨k, hpick k⟩ at hsnd
  have hinj : ∀ (i i' : ι) (a : S i) (a' : S i'),
      i = i' → code i a = code i' a' → a.val = a'.val := by
    intro i i' a a' hii'
    subst i'
    intro haa'
    exact congrArg Subtype.val (hcode i haa')
  exact hinj _ _ ⟨j, hpick j⟩ ⟨k, hpick k⟩ hfst hsnd

/-- Cardinal comparison with the countable factor, with explicit lifts for
independent index universes. The finite case is not collapsed to this bound. -/
theorem lift_mk_le_lift_mk_mul_aleph0_of_surjective
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    {σ : 𝕜 →+* 𝕜} (f : H →ₛₗ[σ] K)
    (hf : Continuous f) (hsurj : Function.Surjective f) :
    Cardinal.lift.{uI} (#κ) ≤ Cardinal.lift.{uJ} (#ι * Cardinal.aleph0) := by
  have h := Cardinal.lift_mk_le'.mpr
    (b.nonempty_embedding_prod_nat_of_surjective c f hf hsurj)
  simpa only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat,
    Cardinal.lift_aleph0] using h

/-- A finite Hilbert basis transported by an algebraic semilinear equivalence
is a genuine finite algebraic basis. No norm or continuity is assumed here. -/
def finiteBasisMap [Fintype ι] (b : HilbertBasis ι 𝕜 H)
    {σ : 𝕜 ≃+* 𝕜} (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) : Module.Basis ι 𝕜 K := by
  classical
  have hi : LinearIndependent 𝕜 (fun i => e (b i)) := by
    apply Fintype.linearIndependent_iffₛ.mpr
    intro a d had i
    have hsum : (∑ j, σ.symm (a j) • b j) = ∑ j, σ.symm (d j) • b j := by
      have hterm (c : 𝕜) (j : ι) : e.symm (c • e (b j)) = σ.symm c • b j := by
        rw [e.symm.map_smulₛₗ]
        change σ.symm c • e.symm (e (b j)) = σ.symm c • b j
        rw [e.symm_apply_apply]
      simpa only [map_sum, hterm] using congrArg e.symm had
    exact σ.symm.injective
      (Fintype.linearIndependent_iffₛ.mp b.orthonormal.linearIndependent _ _ hsum i)
  have hsp : (⊤ : Submodule 𝕜 K) ≤ Submodule.span 𝕜 (Set.range fun i => e (b i)) := by
    intro z _
    obtain ⟨x, rfl⟩ := e.surjective z
    have hsum : (∑ i, b.repr x i • b i) = x :=
      (hasSum_fintype _).unique (b.hasSum_repr x)
    rw [← hsum, map_sum]
    apply Submodule.sum_mem _
    intro i _
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Module.Basis.mk hi hsp

@[simp]
theorem finiteBasisMap_apply [Fintype ι] (b : HilbertBasis ι 𝕜 H)
    {σ : 𝕜 ≃+* 𝕜} (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) (i : ι) :
    b.finiteBasisMap e i = e (b i) := by
  unfold finiteBasisMap
  rw [Module.Basis.mk_apply]

/-- Finite index comparison, including the empty basis of the zero space.
The target index is proved finite before its cardinality is calculated. -/
theorem lift_mk_eq_of_finite (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    [Finite ι] {σ : 𝕜 ≃+* 𝕜} (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let d : Module.Basis ι 𝕜 K := b.finiteBasisMap e
  letI : Module.Finite 𝕜 K := Module.Finite.of_basis d
  letI : Finite κ := c.orthonormal.linearIndependent.finite
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card ι = Fintype.card κ :=
    (Module.finrank_eq_card_basis d).symm.trans
      (Module.finrank_eq_card_basis c.toOrthonormalBasis.toBasis)
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, hcard]

/-- Actual Hilbert-basis index cardinality is preserved by a continuous
semilinear equivalence with continuous inverse. No separability or finite
dimensionality hypothesis is imposed, and the scalar automorphism itself
need not be separately assumed continuous or isometric. -/
theorem lift_mk_eq_of_continuous_semilinear_equiv
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    {σ : 𝕜 ≃+* 𝕜} (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K)
    (he : Continuous e) (he' : Continuous e.symm) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  classical
  rcases finite_or_infinite ι with hi | hi
  · letI : Finite ι := hi
    exact b.lift_mk_eq_of_finite c e
  · letI : Infinite ι := hi
    rcases finite_or_infinite κ with hj | hj
    · letI : Finite κ := hj
      exact (c.lift_mk_eq_of_finite b e.symm).symm
    · letI : Infinite κ := hj
      apply le_antisymm
      · have h := c.lift_mk_le_lift_mk_mul_aleph0_of_surjective
          b e.symm.toLinearMap he' e.symm.surjective
        simpa only [Cardinal.mk_mul_aleph0_eq (α := κ)] using h
      · have h := b.lift_mk_le_lift_mk_mul_aleph0_of_surjective
          c e.toLinearMap he e.surjective
        simpa only [Cardinal.mk_mul_aleph0_eq (α := ι)] using h

/-- The bounded linear-equivalence specialization over the real or complex
field. This does not assert that the given equivalence is isometric. -/
theorem lift_mk_eq_of_continuous_linear_equiv
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K) (e : H ≃L[𝕜] K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) :=
  b.lift_mk_eq_of_continuous_semilinear_equiv c (σ := RingEquiv.refl 𝕜)
    e.toLinearEquiv e.continuous e.symm.continuous

/-- The bounded conjugate-linear specialization over the complex field. -/
theorem lift_mk_eq_of_continuous_conjugate_linear_equiv
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ K)
    (e : ContinuousLinearEquiv (starRingAut (R := ℂ)).toRingHom (σ' := (starRingAut (R := ℂ)).symm.toRingHom) H K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) :=
  b.lift_mk_eq_of_continuous_semilinear_equiv c (σ := starRingAut (R := ℂ))
    e.toLinearEquiv e.continuous e.symm.continuous

/-- Finite-dimensional comparison from an actual finite-dimensional equality.
This lemma never uses the value zero of `finrank` in an infinite-dimensional space. -/
theorem lift_mk_eq_of_finrank_eq
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    [FiniteDimensional 𝕜 H] [FiniteDimensional 𝕜 K]
    (h : Module.finrank 𝕜 H = Module.finrank 𝕜 K) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  classical
  letI : Finite ι := b.orthonormal.linearIndependent.finite
  letI : Finite κ := c.orthonormal.linearIndependent.finite
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card ι = Fintype.card κ :=
    (Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis).symm.trans
      (h.trans (Module.finrank_eq_card_basis c.toOrthonormalBasis.toBasis))
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, hcard]

/-- The equality is equivalently the existence of an index equivalence, with
no equality of the index universes required. -/
theorem nonempty_equiv_of_continuous_semilinear_equiv
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 K)
    {σ : 𝕜 ≃+* 𝕜} (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) H K)
    (he : Continuous e) (he' : Continuous e.symm) : Nonempty (ι ≃ κ) :=
  Cardinal.lift_mk_eq'.mp (b.lift_mk_eq_of_continuous_semilinear_equiv c e he he')

end HilbertBasis
