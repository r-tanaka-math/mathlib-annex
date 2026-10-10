/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.InnerProductSpace.HilbertBasisCardinality
import MathlibAnnex.Analysis.Normed.Operator.ClosureRange
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Hilbert-basis cardinality of dense spans and closed operator ranges

A continuous map into the closure of its range is only asserted to have dense
range. No surjective map or bounded inverse is inferred from density. The
infinite-index proof uses countable coordinate supports; the finite-index proof
uses closedness of a finite-dimensional span. Cardinal lifts permit independent
universes for both spaces and both Hilbert-basis index types.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Cardinal Topology

universe uF uH uK uI uJ

namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type uI} {κ : Type uJ}

/-- A dense spanning family detects every coordinate of an actual Hilbert basis. -/
theorem exists_repr_ne_zero_of_dense_span (b : HilbertBasis κ 𝕜 H)
    (v : ι → H) (hv : (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤)
    (j : κ) : ∃ i, b.repr (v i) j ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  let L : H →L[𝕜] 𝕜 := innerSL 𝕜 (b j)
  have hs : Submodule.span 𝕜 (Set.range v) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner 𝕜 (b j) (v i) = 0
    simpa only [HilbertBasis.repr_apply_apply] using h i
  have hc : (Submodule.span 𝕜 (Set.range v)).topologicalClosure ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hs L.isClosed_ker
  rw [hv] at hc
  have hz : inner 𝕜 (b j) (b j) = 0 := hc (Submodule.mem_top : b j ∈ (⊤ : Submodule 𝕜 H))
  exact b.orthonormal.linearIndependent.ne_zero j (inner_self_eq_zero.mp hz)

/-- Countable coordinate supports give a concrete embedding. No independence
of the dense spanning family is needed. -/
theorem nonempty_embedding_prod_nat_of_dense_span (b : HilbertBasis κ 𝕜 H)
    (v : ι → H) (hv : (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤) :
    Nonempty (κ ↪ ι × ℕ) := by
  classical
  let S : ι → Set κ := fun i => Function.support (fun j => b.repr (v i) j)
  have hc : ∀ i, (S i).Countable := fun i => b.countable_support_repr (v i)
  have hcode : ∀ i, ∃ f : S i → ℕ, Function.Injective f := by
    intro i
    letI : Countable (S i) := (hc i).to_subtype
    exact Countable.exists_injective_nat (S i)
  choose code hcode using hcode
  have hcover : ∀ j : κ, ∃ i, j ∈ S i := b.exists_repr_ne_zero_of_dense_span v hv
  choose pick hpick using hcover
  refine ⟨⟨fun j => (pick j, code (pick j) ⟨j, hpick j⟩), ?_⟩⟩
  intro j k h
  have h₁ : pick j = pick k := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have hinj : ∀ (i i' : ι) (a : S i) (a' : S i'),
      i = i' → code i a = code i' a' → a.val = a'.val := by
    intro i i' a a' hii'
    subst i'
    intro haa'
    exact congrArg Subtype.val (hcode i haa')
  exact hinj _ _ ⟨j, hpick j⟩ ⟨k, hpick k⟩ h₁ h₂

/-- The number of Hilbert-basis vectors is bounded by the number of dense
span generators. Empty and finite families are handled before cardinal
multiplication by `aleph0` is used. -/
theorem lift_mk_le_of_dense_span (b : HilbertBasis κ 𝕜 H)
    (v : ι → H) (hv : (Submodule.span 𝕜 (Set.range v)).topologicalClosure = ⊤) :
    Cardinal.lift.{uI} (#κ) ≤ Cardinal.lift.{uJ} (#ι) := by
  classical
  rcases finite_or_infinite ι with hi | hi
  · letI : Finite ι := hi
    letI : Fintype ι := Fintype.ofFinite ι
    let L : Submodule 𝕜 H := Submodule.span 𝕜 (Set.range v)
    have hfg : L.FG := ⟨(Set.finite_range v).toFinset, by simp [L]⟩
    letI : Module.Finite 𝕜 L := Module.Finite.of_fg hfg
    have hcl : IsClosed (L : Set H) := Submodule.closed_of_finiteDimensional L
    have heq : L.topologicalClosure = L := by
      apply SetLike.coe_injective
      simpa only [Submodule.topologicalClosure_coe] using hcl.closure_eq
    have htop : L = ⊤ := heq.symm.trans hv
    letI : Module.Finite 𝕜 H := Module.Finite.of_fg_top (htop ▸ hfg)
    letI : Finite κ := b.orthonormal.linearIndependent.finite
    letI : Fintype κ := Fintype.ofFinite κ
    have hn : Fintype.card κ ≤ Fintype.card ι := by
      rw [← Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis]
      exact finrank_le_of_span_eq_top htop
    simp only [Cardinal.mk_fintype, Cardinal.lift_natCast]
    exact_mod_cast hn
  · letI : Infinite ι := hi
    have h := Cardinal.lift_mk_le'.mpr
      (b.nonempty_embedding_prod_nat_of_dense_span v hv)
    simpa only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat,
      Cardinal.lift_aleph0, Cardinal.mk_mul_aleph0_eq] using h

variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- A continuous linear map with dense range cannot increase Hilbert-basis
cardinality. Dense range, rather than surjectivity, is the hypothesis. -/
theorem lift_mk_le_of_denseRange (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (T : H →L[𝕜] K) (hT : DenseRange T) :
    Cardinal.lift.{uI} (#κ) ≤ Cardinal.lift.{uJ} (#ι) := by
  let L : Submodule 𝕜 K := (Submodule.span 𝕜 (Set.range fun i => T (b i))).topologicalClosure
  have hL : IsClosed (L : Set K) :=
    (Submodule.span 𝕜 (Set.range fun i => T (b i))).isClosed_topologicalClosure
  have hs : Submodule.span 𝕜 (Set.range b) ≤ L.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Submodule.span 𝕜 (Set.range fun i => T (b i))).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)
  have hc : (Submodule.span 𝕜 (Set.range b)).topologicalClosure ≤
      L.comap T.toLinearMap :=
    Submodule.topologicalClosure_minimal _ hs (hL.preimage T.continuous)
  rw [b.dense_span] at hc
  have hr : Set.range T ⊆ (L : Set K) := by
    rintro _ ⟨x, rfl⟩
    exact hc (Submodule.mem_top : x ∈ (⊤ : Submodule 𝕜 H))
  have ht : L = ⊤ := by
    apply top_unique
    intro y _
    exact (closure_minimal hr hL) (hT y)
  exact c.lift_mk_le_of_dense_span (fun i => T (b i)) ht

end HilbertBasis


namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable {ι : Type uI} {κ : Type uJ}

/-- Luft's dimension inequality for the norm closure of the actual operator
range. Both sides refer to given Hilbert bases, in independent universes. -/
theorem lift_mk_le_closure_range (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (c : HilbertBasis κ 𝕜 T.range.topologicalClosure) :
    Cardinal.lift.{uI} (#κ) ≤ Cardinal.lift.{uJ} (#ι) :=
  b.lift_mk_le_of_denseRange c T.toClosureRange T.denseRange_toClosureRange

/-- Cardinality is monotone under inclusion of closed subspaces, using an
actual surjective orthogonal projection rather than an inverse to the inclusion. -/
theorem lift_mk_le_of_submodule_le (M N : Submodule 𝕜 H)
    (hM : IsClosed (M : Set H)) (hN : IsClosed (N : Set H)) (hMN : M ≤ N)
    [CompleteSpace H] (b : HilbertBasis ι 𝕜 M) (c : HilbertBasis κ 𝕜 N) :
    Cardinal.lift.{uJ} (#ι) ≤ Cardinal.lift.{uI} (#κ) := by
  letI : CompleteSpace M := hM.completeSpace_coe
  letI : CompleteSpace N := hN.completeSpace_coe
  let q : N →L[𝕜] M := M.orthogonalProjectionOnto.comp N.subtypeL
  have hq : Surjective q := by
    intro x
    refine ⟨⟨(x : H), hMN x.property⟩, ?_⟩
    change M.orthogonalProjectionOnto (x : H) = x
    exact M.orthogonalProjectionOnto_mem_subspace_eq_self x
  exact c.lift_mk_le_of_denseRange b q hq.denseRange

end HilbertBasis

namespace HilbertBasis

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
variable {ι : Type uI} {κ : Type uJ}

/-- A closed ambient submodule containing every vector of a Hilbert basis
contains the whole subspace on which that basis is defined. -/
theorem submodule_le_of_forall_mem {M N : Submodule 𝕜 H}
    (b : HilbertBasis ι 𝕜 M) (hN : IsClosed (N : Set H))
    (hb : ∀ i, (b i : H) ∈ N) : M ≤ N := by
  have hs : Submodule.span 𝕜 (Set.range b) ≤ N.comap M.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  have hc := Submodule.topologicalClosure_minimal _ hs
    (hN.preimage M.subtypeL.continuous)
  rw [b.dense_span] at hc
  intro x hx
  exact hc (Submodule.mem_top : (⟨x, hx⟩ : M) ∈ (⊤ : Submodule 𝕜 M))

/-- The original generators, viewed in their closed span, still have dense
span. The proof uses closed kernels in the ambient Hilbert space. -/
theorem dense_span_in_closed_span [CompleteSpace H] (v : ι → H) :
    let M := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
    (Submodule.span 𝕜 (Set.range fun i =>
      (⟨v i, (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨i, rfl⟩)⟩ : M))).topologicalClosure = ⊤ := by
  let M := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
  letI : CompleteSpace M := (Submodule.span 𝕜 (Set.range v)).isClosed_topologicalClosure.completeSpace_coe
  let w : ι → M := fun i => ⟨v i, (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
    (Submodule.subset_span ⟨i, rfl⟩)⟩
  change (Submodule.span 𝕜 (Set.range w)).topologicalClosure = ⊤
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm ?_ bot_le
  intro z hz
  have hv : ∀ i, inner 𝕜 (z : H) (v i) = 0 := by
    intro i
    have h := hz (w i) (Submodule.subset_span ⟨i, rfl⟩)
    change inner 𝕜 (v i) (z : H) = 0 at h
    exact inner_eq_zero_symm.mp h
  let f : H →L[𝕜] 𝕜 := innerSL 𝕜 (z : H)
  have hs : Submodule.span 𝕜 (Set.range v) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hm : M ≤ f.ker := Submodule.topologicalClosure_minimal _ hs f.isClosed_ker
  have hz0 : (z : H) = 0 := inner_self_eq_zero.mp (hm z.property)
  exact (Submodule.mem_bot (R := 𝕜) (x := z)).mpr (Subtype.ext hz0)

/-- Cardinality of any Hilbert basis of the closed span of an arbitrary
family. Finite families and zero generators are permitted. -/
theorem lift_mk_le_closed_span [CompleteSpace H] (v : ι → H)
    (b : HilbertBasis κ 𝕜 (Submodule.span 𝕜 (Set.range v)).topologicalClosure) :
    Cardinal.lift.{uI} (#κ) ≤ Cardinal.lift.{uJ} (#ι) := by
  let M := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
  let w : ι → M := fun i => ⟨v i, (Submodule.span 𝕜 (Set.range v)).le_topologicalClosure
    (Submodule.subset_span ⟨i, rfl⟩)⟩
  exact b.lift_mk_le_of_dense_span w (dense_span_in_closed_span v)

universe uA

/-- A dense continuous linear image preserves a strict Hilbert-basis bound,
with all three index/cardinal universes made explicit. -/
theorem lift_mk_lt_of_denseRange (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (T : H →L[𝕜] K) (hT : DenseRange T)
    {α : Cardinal.{uA}} (hb : Cardinal.lift.{uA} (#ι) < Cardinal.lift.{uI} α) :
    Cardinal.lift.{uA} (#κ) < Cardinal.lift.{uJ} α := by
  have hle : Cardinal.lift.{uA} (Cardinal.lift.{uI} (#κ)) ≤
      Cardinal.lift.{uA} (Cardinal.lift.{uJ} (#ι)) :=
    Cardinal.lift_le.mpr (b.lift_mk_le_of_denseRange c T hT)
  have hlt : Cardinal.lift.{uJ} (Cardinal.lift.{uA} (#ι)) <
      Cardinal.lift.{uJ} (Cardinal.lift.{uI} α) := Cardinal.lift_lt.mpr hb
  simp only [Cardinal.lift_lift] at hle hlt
  have h : Cardinal.lift.{uI} (Cardinal.lift.{uA} (#κ)) <
      Cardinal.lift.{uI} (Cardinal.lift.{uJ} α) := by
    simpa only [Cardinal.lift_lift] using hle.trans_lt hlt
  exact Cardinal.lift_lt.mp h

end HilbertBasis

namespace ContinuousLinearMap

variable {𝕜 : Type uF} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {K : Type uK} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

/-- Restrict an operator to the closed range of its adjoint and corestrict it
to its own closed range. The map need not have bounded inverse. -/
def adjointClosureRangeRestriction (T : H →L[𝕜] K) :
    T.adjoint.range.topologicalClosure →L[𝕜] T.range.topologicalClosure :=
  T.toClosureRange.comp T.adjoint.range.topologicalClosure.subtypeL

/-- This restriction has dense range. Surjectivity onto the closed range is
not asserted: only the original, possibly nonclosed range is covered. -/
theorem denseRange_adjointClosureRangeRestriction (T : H →L[𝕜] K) :
    DenseRange T.adjointClosureRangeRestriction := by
  let M := T.adjoint.range.topologicalClosure
  letI : CompleteSpace M := T.adjoint.range.isClosed_topologicalClosure.completeSpace_coe
  letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have horth : Mᗮ = T.ker := by
    rw [show M = T.kerᗮ from T.orthogonal_ker.symm, Submodule.orthogonal_orthogonal]
  have hr : Set.range T.toClosureRange ⊆ Set.range T.adjointClosureRangeRestriction := by
    rintro _ ⟨x, rfl⟩
    have hz : T (x - M.starProjection x) = 0 := by
      have h : x - M.starProjection x ∈ Mᗮ :=
        Submodule.sub_starProjection_mem_orthogonal x
      rw [horth] at h
      exact h
    have hx : T (M.starProjection x) = T x := by
      exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm
    refine ⟨M.orthogonalProjectionOnto x, ?_⟩
    exact Subtype.ext hx
  intro y
  exact (closure_mono hr) (T.denseRange_toClosureRange y)

/-- The closed ranges of an operator and its adjoint have the same Hilbert
basis cardinality. The two dense restrictions, not a polar decomposition or
an assumed bounded inverse, supply the two inequalities. -/
theorem hilbertBasis_lift_mk_eq_closure_range_adjoint (T : H →L[𝕜] K)
    {ι : Type uI} {κ : Type uJ}
    (b : HilbertBasis ι 𝕜 T.range.topologicalClosure)
    (c : HilbertBasis κ 𝕜 T.adjoint.range.topologicalClosure) :
    Cardinal.lift.{uJ} (#ι) = Cardinal.lift.{uI} (#κ) := by
  apply le_antisymm
  · exact c.lift_mk_le_of_denseRange b T.adjointClosureRangeRestriction
      T.denseRange_adjointClosureRangeRestriction
  · have hex : ∃ q : T.adjoint.adjoint.range.topologicalClosure →L[𝕜]
        T.adjoint.range.topologicalClosure, DenseRange q :=
      ⟨T.adjoint.adjointClosureRangeRestriction,
        T.adjoint.denseRange_adjointClosureRangeRestriction⟩
    rw [adjoint_adjoint] at hex
    obtain ⟨q, hq⟩ := hex
    exact b.lift_mk_le_of_denseRange c q hq

end ContinuousLinearMap
