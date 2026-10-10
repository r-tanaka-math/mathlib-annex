/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.LinearAlgebra.Projectivization.FiniteSpan
import Mathlib.Order.CompleteLattice.Basic

/-!
# Subspace order transport from finite projective incidence

Only the new transport between two projective spaces is constructed here.
The existing `Projectivization.Subspace.submodule` order isomorphism supplies
the correspondence with ALL algebraic submodules, without any topology.
The finite-incidence premise is explicit; its normal-part specialization and
a semilinear realization are separate mathematical obligations.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

universe uK uL uV uW uI
variable {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
variable [DivisionRing K] [DivisionRing L]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
variable (e : ℙ K V ≃ ℙ L W)
variable (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
  p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))

namespace Subspace

/-- The literal image of a projective subspace is again a projective subspace.
The addition axiom follows from finite incidence, not an assumed linear lift. -/
def mapOfFiniteSpan (P : Subspace K V) : Subspace L W where
  carrier := e '' (P : Set (ℙ K V))
  mem_add' v w hv hw hvw hvP hwP := by
    have hz : Projectivization.mk L (v + w) hvw ∈ span (e '' (P : Set (ℙ K V))) :=
      (span (e '' (P : Set (ℙ K V)))).mem_add v w hv hw hvw
        (subset_span _ hvP) (subset_span _ hwP)
    have hin : e.symm (Projectivization.mk L (v + w) hvw) ∈ span (P : Set (ℙ K V)) :=
      (mem_span_image_iff_of_finite_span e he _ _).mpr
        (by simpa only [e.apply_symm_apply] using hz)
    exact ⟨e.symm (Projectivization.mk L (v + w) hvw), by simpa only [span_coe, SetLike.mem_coe] using hin,
      e.apply_symm_apply _⟩

/-- The underlying set is an image, with no extra span or closure added. -/
@[simp]
theorem coe_mapOfFiniteSpan (P : Subspace K V) :
    (mapOfFiniteSpan e he P : Set (ℙ L W)) = e '' (P : Set (ℙ K V)) := rfl

/-- Membership uses the actual inverse point map. -/
@[simp]
theorem mem_mapOfFiniteSpan_iff (P : Subspace K V) (q : ℙ L W) :
    q ∈ mapOfFiniteSpan e he P ↔ e.symm q ∈ P := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p ∈ P at hp
    simpa only [e.symm_apply_apply] using hp
  · intro hq
    exact ⟨e.symm q, hq, e.apply_symm_apply q⟩

/-- The inverse transport is the image by the inverse point equivalence. -/
def comapOfFiniteSpan (Q : Subspace L W) : Subspace K V :=
  mapOfFiniteSpan e.symm (finite_span_symm_iff e he) Q

/-- Equivalently, inverse transport has the literal preimage carrier. -/
@[simp]
theorem coe_comapOfFiniteSpan (Q : Subspace L W) :
    (comapOfFiniteSpan e he Q : Set (ℙ K V)) = e ⁻¹' (Q : Set (ℙ L W)) := by
  ext p
  exact mem_mapOfFiniteSpan_iff e.symm (finite_span_symm_iff e he) Q p

@[simp]
theorem mem_comapOfFiniteSpan_iff (Q : Subspace L W) (p : ℙ K V) :
    p ∈ comapOfFiniteSpan e he Q ↔ e p ∈ Q := by
  rw [← SetLike.mem_coe, coe_comapOfFiniteSpan]
  rfl

@[simp]
theorem comapOfFiniteSpan_mapOfFiniteSpan (P : Subspace K V) :
    comapOfFiniteSpan e he (mapOfFiniteSpan e he P) = P := by
  apply SetLike.coe_injective
  ext p
  simp only [SetLike.mem_coe, mem_comapOfFiniteSpan_iff, mem_mapOfFiniteSpan_iff,
    e.symm_apply_apply]

@[simp]
theorem mapOfFiniteSpan_comapOfFiniteSpan (Q : Subspace L W) :
    mapOfFiniteSpan e he (comapOfFiniteSpan e he Q) = Q := by
  apply SetLike.coe_injective
  ext q
  simp only [SetLike.mem_coe, mem_mapOfFiniteSpan_iff, mem_comapOfFiniteSpan_iff,
    e.apply_symm_apply]

/-- The projective-subspace order isomorphism induced by the given point map. -/
def orderIsoOfFiniteSpan : Subspace K V ≃o Subspace L W where
  toFun := mapOfFiniteSpan e he
  invFun := comapOfFiniteSpan e he
  left_inv := comapOfFiniteSpan_mapOfFiniteSpan e he
  right_inv := mapOfFiniteSpan_comapOfFiniteSpan e he
  map_rel_iff' := by
    intro P Q
    constructor
    · intro h p hp
      have hx : e p ∈ mapOfFiniteSpan e he P := ⟨p, hp, rfl⟩
      have hy : e p ∈ mapOfFiniteSpan e he Q := h hx
      simpa only [e.symm_apply_apply] using (mem_mapOfFiniteSpan_iff e he Q (e p)).mp hy
    · intro h q hq
      exact (mem_mapOfFiniteSpan_iff e he Q q).mpr
        (h ((mem_mapOfFiniteSpan_iff e he P q).mp hq))

/-- All spans, not merely finite spans, are transported by the same map. -/
@[simp]
theorem orderIsoOfFiniteSpan_span (S : Set (ℙ K V)) :
    orderIsoOfFiniteSpan e he (span S) = span (e '' S) := by
  apply SetLike.coe_injective
  exact image_span_eq_of_finite_span e he S

/-- The inverse is exactly the transport defined from the inverse point map. -/
theorem orderIsoOfFiniteSpan_symm :
    (orderIsoOfFiniteSpan e he).symm =
      orderIsoOfFiniteSpan e.symm (finite_span_symm_iff e he) := by
  apply DFunLike.ext
  intro Q
  rfl

end Subspace

/-- Algebraic submodule transport, composed with Mathlib's existing
projective-subspace/submodule order isomorphisms on both sides. -/
def submoduleOrderIsoOfFiniteSpan : Submodule K V ≃o Submodule L W :=
  (Submodule.projectivization (K := K) (V := V)).trans
    ((Subspace.orderIsoOfFiniteSpan e he).trans
      (Subspace.submodule (K := L) (V := W)))

/-- The inverse algebraic order map is the map induced by the inverse point map. -/
theorem submoduleOrderIsoOfFiniteSpan_symm :
    (submoduleOrderIsoOfFiniteSpan e he).symm =
      submoduleOrderIsoOfFiniteSpan e.symm (Subspace.finite_span_symm_iff e he) := by
  apply DFunLike.ext
  intro Q
  rfl

/-- The projectivization of a transported submodule is the actual image. -/
@[simp]
theorem projectivization_submoduleOrderIsoOfFiniteSpan (P : Submodule K V) :
    (submoduleOrderIsoOfFiniteSpan e he P).projectivization =
      Subspace.mapOfFiniteSpan e he P.projectivization := by
  change Subspace.submodule.symm (Subspace.submodule _) = _
  exact Subspace.submodule.symm_apply_apply _

/-- Point membership in the transported algebraic submodule. -/
theorem mem_projectivization_submoduleOrderIsoOfFiniteSpan_iff
    (P : Submodule K V) (q : ℙ L W) :
    q ∈ (submoduleOrderIsoOfFiniteSpan e he P).projectivization ↔
      e.symm q ∈ P.projectivization := by
  rw [projectivization_submoduleOrderIsoOfFiniteSpan, Subspace.mem_mapOfFiniteSpan_iff]

/-- Evaluation on a nonzero vector; no representative of the zero vector is used. -/
theorem mem_submoduleOrderIsoOfFiniteSpan_iff (P : Submodule K V)
    (w : W) (hw : w ≠ 0) :
    w ∈ submoduleOrderIsoOfFiniteSpan e he P ↔
      e.symm (Projectivization.mk L w hw) ∈ P.projectivization := by
  rw [← Submodule.mk_mem_projectivization_iff _ hw,
    mem_projectivization_submoduleOrderIsoOfFiniteSpan_iff]

/-- Explicit inverse evaluation via the original projective point map. -/
theorem mem_symm_submoduleOrderIsoOfFiniteSpan_iff (Q : Submodule L W)
    (v : V) (hv : v ≠ 0) :
    v ∈ (submoduleOrderIsoOfFiniteSpan e he).symm Q ↔
      e (mk K v hv) ∈ Q.projectivization := by
  change v ∈ Subspace.submodule (Subspace.comapOfFiniteSpan e he Q.projectivization) ↔ _
  rw [Subspace.mem_submodule_iff _ hv, Subspace.mem_comapOfFiniteSpan_iff]

/-- The transported submodule contains zero even when there are no projective points. -/
theorem zero_mem_submoduleOrderIsoOfFiniteSpan (P : Submodule K V) :
    (0 : W) ∈ submoduleOrderIsoOfFiniteSpan e he P :=
  (submoduleOrderIsoOfFiniteSpan e he P).zero_mem

/-- On one-dimensional submodules the order map is precisely the input point map. -/
@[simp]
theorem submoduleOrderIsoOfFiniteSpan_submodule (p : ℙ K V) :
    submoduleOrderIsoOfFiniteSpan e he p.submodule = (e p).submodule := by
  apply (Submodule.projectivization (K := L) (V := W)).injective
  rw [projectivization_submoduleOrderIsoOfFiniteSpan]
  apply SetLike.coe_injective
  rw [Subspace.coe_mapOfFiniteSpan, Subspace.coe_projectivization_submodule,
    Set.image_singleton, Subspace.coe_projectivization_submodule]

/-- Formula for a line specified by any nonzero vector. -/
theorem submoduleOrderIsoOfFiniteSpan_span_singleton (v : V) (hv : v ≠ 0) :
    submoduleOrderIsoOfFiniteSpan e he (K ∙ v) = (e (mk K v hv)).submodule :=
  submoduleOrderIsoOfFiniteSpan_submodule e he (mk K v hv)

/-- Explicit inverse law on all submodules, not just finite-dimensional ones. -/
@[simp]
theorem symm_apply_submoduleOrderIsoOfFiniteSpan (P : Submodule K V) :
    (submoduleOrderIsoOfFiniteSpan e he).symm (submoduleOrderIsoOfFiniteSpan e he P) = P :=
  (submoduleOrderIsoOfFiniteSpan e he).symm_apply_apply P

@[simp]
theorem apply_symm_submoduleOrderIsoOfFiniteSpan (Q : Submodule L W) :
    submoduleOrderIsoOfFiniteSpan e he ((submoduleOrderIsoOfFiniteSpan e he).symm Q) = Q :=
  (submoduleOrderIsoOfFiniteSpan e he).apply_symm_apply Q

/-- Order preservation and reflection. -/
theorem submoduleOrderIsoOfFiniteSpan_le_iff (P Q : Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he P ≤ submoduleOrderIsoOfFiniteSpan e he Q ↔ P ≤ Q :=
  (submoduleOrderIsoOfFiniteSpan e he).le_iff_le

@[simp]
theorem submoduleOrderIsoOfFiniteSpan_bot :
    submoduleOrderIsoOfFiniteSpan e he ⊥ = ⊥ :=
  (submoduleOrderIsoOfFiniteSpan e he).map_bot

@[simp]
theorem submoduleOrderIsoOfFiniteSpan_top :
    submoduleOrderIsoOfFiniteSpan e he ⊤ = ⊤ :=
  (submoduleOrderIsoOfFiniteSpan e he).map_top

/-- Arbitrary algebraic generation, expressed with actual projective representatives. -/
theorem submoduleOrderIsoOfFiniteSpan_span_rep_image (S : Set (ℙ K V)) :
    submoduleOrderIsoOfFiniteSpan e he (Submodule.span K (Projectivization.rep '' S)) =
      Submodule.span L (Projectivization.rep '' (e '' S)) := by
  rw [← Subspace.submodule_span_eq_span_rep_image,
    ← Subspace.submodule_span_eq_span_rep_image]
  change Subspace.submodule
    (Subspace.orderIsoOfFiniteSpan e he
      (Subspace.submodule.symm (Subspace.submodule (Subspace.span S)))) = _
  rw [Subspace.submodule.symm_apply_apply, Subspace.orderIsoOfFiniteSpan_span]

/-- Binary joins are transported in the complete algebraic submodule lattice. -/
theorem submoduleOrderIsoOfFiniteSpan_sup (P Q : Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he (P ⊔ Q) =
      submoduleOrderIsoOfFiniteSpan e he P ⊔ submoduleOrderIsoOfFiniteSpan e he Q :=
  (submoduleOrderIsoOfFiniteSpan e he).map_sup P Q

/-- Binary meets are transported. -/
theorem submoduleOrderIsoOfFiniteSpan_inf (P Q : Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he (P ⊓ Q) =
      submoduleOrderIsoOfFiniteSpan e he P ⊓ submoduleOrderIsoOfFiniteSpan e he Q :=
  (submoduleOrderIsoOfFiniteSpan e he).map_inf P Q

/-- Arbitrary joins, including an empty indexed family. -/
theorem submoduleOrderIsoOfFiniteSpan_iSup {ι : Sort uI} (P : ι → Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he (⨆ i, P i) =
      ⨆ i, submoduleOrderIsoOfFiniteSpan e he (P i) :=
  (submoduleOrderIsoOfFiniteSpan e he).map_iSup P

/-- Arbitrary meets, including an empty indexed family. -/
theorem submoduleOrderIsoOfFiniteSpan_iInf {ι : Sort uI} (P : ι → Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he (⨅ i, P i) =
      ⨅ i, submoduleOrderIsoOfFiniteSpan e he (P i) :=
  (submoduleOrderIsoOfFiniteSpan e he).map_iInf P

/-- The same arbitrary-join formula for an unindexed set of submodules. -/
theorem submoduleOrderIsoOfFiniteSpan_sSup (S : Set (Submodule K V)) :
    submoduleOrderIsoOfFiniteSpan e he (sSup S) = sSup (submoduleOrderIsoOfFiniteSpan e he '' S) := by
  rw [sSup_image]
  exact (submoduleOrderIsoOfFiniteSpan e he).map_sSup S

/-- The same arbitrary-meet formula for an unindexed set of submodules. -/
theorem submoduleOrderIsoOfFiniteSpan_sInf (S : Set (Submodule K V)) :
    submoduleOrderIsoOfFiniteSpan e he (sInf S) = sInf (submoduleOrderIsoOfFiniteSpan e he '' S) := by
  rw [sInf_image]
  exact (submoduleOrderIsoOfFiniteSpan e he).map_sInf S

end Projectivization
