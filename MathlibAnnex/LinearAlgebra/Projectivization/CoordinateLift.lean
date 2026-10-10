/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.LinearAlgebra.Projectivization.Dimension
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Coordinates on projective pencils

A finite-span preserving point equivalence induces actual scalar equivalences
on every coordinate pencil. The target basis can be normalized simultaneously
at an anchor so that the parameter `1` is fixed on each anchor pencil.

All bases may have arbitrary index types. The point map is the given equivalence,
not the projectivization of an unproved linear or semilinear lift. At this stage
the scalar maps are equivalences of sets; ring laws are not asserted.

This coordinate construction is stated over fields. It does not change the
DivisionRing generality of the imported subspace and dimension transport.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization
open scoped Classical

namespace Projectivization

universe uK uL uV uW uI
variable {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
variable [Field K] [Field L]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
variable {ι : Type uI}

/-- A representative normalized to have coordinate `i` equal to one whenever
that coordinate is nonzero. The zero-coordinate case is not a projective chart. -/
def coordinateRepresentative (b : Module.Basis ι K V) (i : ι) (p : ℙ K V) : V :=
  (b.repr p.rep i)⁻¹ • p.rep

/-- Normalization is nonzero on its actual coordinate chart. -/
theorem coordinateRepresentative_ne_zero (b : Module.Basis ι K V) (i : ι)
    (p : ℙ K V) (hp : b.repr p.rep i ≠ 0) :
    coordinateRepresentative b i p ≠ 0 :=
  smul_ne_zero (inv_ne_zero hp) p.rep_nonzero

/-- The chosen coordinate of a chart representative is one. -/
@[simp]
theorem repr_coordinateRepresentative_self (b : Module.Basis ι K V) (i : ι)
    (p : ℙ K V) (hp : b.repr p.rep i ≠ 0) :
    b.repr (coordinateRepresentative b i p) i = 1 := by
  simp [coordinateRepresentative, hp]

/-- Normalizing a representative does not change its projective point. -/
theorem mk_coordinateRepresentative (b : Module.Basis ι K V) (i : ι)
    (p : ℙ K V) (hp : b.repr p.rep i ≠ 0) :
    mk K (coordinateRepresentative b i p) (coordinateRepresentative_ne_zero b i p hp) = p := by
  exact ((mk_eq_mk_iff' K _ p.rep
    (coordinateRepresentative_ne_zero b i p hp) p.rep_nonzero).mpr
      ⟨(b.repr p.rep i)⁻¹, rfl⟩).trans p.mk_rep

/-- Two representatives of the same point with the same coordinate equal to one
are equal as vectors. No choice of scale remains. -/
theorem eq_of_mk_eq_of_repr_eq_one (b : Module.Basis ι K V) (i : ι)
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvi : b.repr v i = 1) (hwi : b.repr w i = 1)
    (h : mk K v hv = mk K w hw) : v = w := by
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' K v w hv hw).mp h
  have ha1 : a = 1 := by
    have hcoord := congrArg (fun z : V => b.repr z i) ha
    simpa [hvi, hwi] using hcoord
  simpa [ha1] using ha.symm

/-- A vector already normalized at coordinate `i` is recovered exactly. -/
theorem coordinateRepresentative_mk (b : Module.Basis ι K V) (i : ι)
    (v : V) (hv : v ≠ 0) (hvi : b.repr v i = 1) :
    coordinateRepresentative b i (mk K v hv) = v := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  have hp : b.repr (mk K v hv).rep i ≠ 0 := by
    rw [← ha]
    simpa [hvi, Units.smul_def] using a.ne_zero
  exact eq_of_mk_eq_of_repr_eq_one b i
    (coordinateRepresentative_ne_zero b i _ hp) hv
    (repr_coordinateRepresentative_self b i _ hp) hvi
    (mk_coordinateRepresentative b i _ hp)

private theorem mem_span_basis_image_iff (b : Module.Basis ι K V)
    (s : Set ι) (v : V) :
    v ∈ Submodule.span K (b '' s) ↔ ∀ i, i ∉ s → b.repr v i = 0 := by
  rw [b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (Finsupp.mem_support_iff.mpr hne))
  · intro h i hi
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hi) (h i hnot)

/-- A coordinate pencil vector has nonzero anchor coordinate, for every scalar. -/
theorem basis_add_smul_ne_zero (b : Module.Basis ι K V) (i j : ι) (hij : i ≠ j) (a : K) :
    b i + a • b j ≠ 0 := by
  intro h
  have hcoord := congrArg (fun v : V => b.repr v i) h
  simpa [hij, hij.symm] using hcoord

/-- The affine part of the coordinate projective line, with `j` the omitted
point and `i` the anchor. -/
def basisPencilPoint (b : Module.Basis ι K V) (i j : ι) (hij : i ≠ j) (a : K) : ℙ K V :=
  mk K (b i + a • b j) (basis_add_smul_ne_zero b i j hij a)

/-- The zero parameter is the anchor point. -/
@[simp]
theorem basisPencilPoint_zero (b : Module.Basis ι K V) (i j : ι) (hij : i ≠ j) :
    basisPencilPoint b i j hij 0 = mk K (b i) (b.ne_zero i) := by
  simp [basisPencilPoint]

/-- Coordinate-pencil parameters are unique. -/
theorem basisPencilPoint_injective (b : Module.Basis ι K V) (i j : ι) (hij : i ≠ j) :
    Function.Injective (basisPencilPoint b i j hij) := by
  intro a d h
  obtain ⟨t, ht⟩ := (mk_eq_mk_iff' K _ _
    (basis_add_smul_ne_zero b i j hij a) (basis_add_smul_ne_zero b i j hij d)).mp h
  have ht1 : t = 1 := by
    have hc := congrArg (fun v : V => b.repr v i) ht
    simpa [hij, hij.symm] using hc
  have hc := congrArg (fun v : V => b.repr v j) ht
  simpa [ht1, hij, hij.symm] using hc.symm

variable (e : ℙ K V ≃ ℙ L W)
variable (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
  p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
variable (b : Module.Basis ι K V) (c : Module.Basis ι L W)
variable (hbc : ∀ i, e (mk K (b i) (b.ne_zero i)) = mk L (c i) (c.ne_zero i))
include he hbc

/-- The same algebraic order map sends every coordinate subspace to the
corresponding target coordinate subspace, including infinitely generated ones. -/
theorem submoduleOrderIsoOfFiniteSpan_span_basis_image (s : Set ι) :
    submoduleOrderIsoOfFiniteSpan e he (Submodule.span K (b '' s)) =
      Submodule.span L (c '' s) := by
  calc
    submoduleOrderIsoOfFiniteSpan e he (Submodule.span K (b '' s)) =
        submoduleOrderIsoOfFiniteSpan e he (⨆ i ∈ s, K ∙ b i) := by
          rw [Submodule.span_eq_iSup_of_singleton_spans, iSup_image]
    _ = ⨆ i ∈ s, L ∙ c i := by
      simp_rw [submoduleOrderIsoOfFiniteSpan_iSup,
        submoduleOrderIsoOfFiniteSpan_span_singleton e he _ (b.ne_zero _), hbc,
        submodule_mk]
    _ = Submodule.span L (c '' s) := by
      rw [Submodule.span_eq_iSup_of_singleton_spans, iSup_image]

/-- Coordinate support is transported by the actual point map. The assertion
is about a representative of `e [v]`, not a presumed vector map. -/
theorem image_rep_mem_span_basis_image_iff (s : Set ι) (v : V) (hv : v ≠ 0) :
    (e (mk K v hv)).rep ∈ Submodule.span L (c '' s) ↔
      v ∈ Submodule.span K (b '' s) := by
  rw [← submoduleOrderIsoOfFiniteSpan_span_basis_image e he b c hbc]
  rw [mem_submoduleOrderIsoOfFiniteSpan_iff e he _ _ (rep_nonzero _),
    mk_rep, e.symm_apply_apply, Submodule.mk_mem_projectivization_iff]

/-- Vanishing of each coordinate is invariant under projective transport in
corresponding bases. This also controls the omitted point of a pencil. -/
theorem repr_image_rep_eq_zero_iff (v : V) (hv : v ≠ 0) (i : ι) :
    c.repr (e (mk K v hv)).rep i = 0 ↔ b.repr v i = 0 := by
  have h := image_rep_mem_span_basis_image_iff e he b c hbc ({i}ᶜ) v hv
  rw [mem_span_basis_image_iff, mem_span_basis_image_iff] at h
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not,
    forall_eq] using h

/-- The image of every affine-pencil point still has a nonzero anchor coordinate. -/
theorem repr_image_basisPencilPoint_ne_zero (i j : ι) (hij : i ≠ j) (a : K) :
    c.repr (e (basisPencilPoint b i j hij a)).rep i ≠ 0 := by
  rw [basisPencilPoint]
  have h := repr_image_rep_eq_zero_iff e he b c hbc
    (b i + a • b j) (basis_add_smul_ne_zero b i j hij a) i
  intro hz
  have hz' := h.mp hz
  simpa [hij, hij.symm] using hz'

omit he hbc in
/-- The parameter read from the normalized image of the coordinate pencil.
This is a function of sets of scalars; ring operations are not yet preserved. -/
def pencilScalar (i j : ι) (hij : i ≠ j) (a : K) : L :=
  c.repr (coordinateRepresentative c i (e (basisPencilPoint b i j hij a))) j

/-- Normalized image vectors on each pencil have exactly two coordinates. -/
theorem coordinateRepresentative_image_basisPencilPoint
    (i j : ι) (hij : i ≠ j) (a : K) :
    coordinateRepresentative c i (e (basisPencilPoint b i j hij a)) =
      c i + pencilScalar e b c i j hij a • c j := by
  have hi := repr_image_basisPencilPoint_ne_zero e he b c hbc i j hij a
  have hv : b i + a • b j ∈ Submodule.span K (b '' ({i, j} : Set ι)) := by
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨i, by simp, rfl⟩
    · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨j, by simp, rfl⟩)
  have hw : (e (basisPencilPoint b i j hij a)).rep ∈
      Submodule.span L (c '' ({i, j} : Set ι)) :=
    (image_rep_mem_span_basis_image_iff e he b c hbc _ _
      (basis_add_smul_ne_zero b i j hij a)).mpr hv
  have hn : coordinateRepresentative c i (e (basisPencilPoint b i j hij a)) ∈
      Submodule.span L (c '' ({i, j} : Set ι)) :=
    Submodule.smul_mem _ _ hw
  apply c.repr.injective
  ext k
  by_cases hki : k = i
  · subst k
    simp [repr_coordinateRepresentative_self c i _ hi, hij, hij.symm]
  by_cases hkj : k = j
  · subst k
    simp [pencilScalar, hij, hij.symm]
  have hz := (mem_span_basis_image_iff c {i, j} _).mp hn k (by simp [hki, hkj])
  simp [hz, hki, hkj, Ne.symm hki, Ne.symm hkj]

/-- Exact projective evaluation of the parameter function on the whole pencil. -/
theorem image_basisPencilPoint (i j : ι) (hij : i ≠ j) (a : K) :
    e (basisPencilPoint b i j hij a) =
      basisPencilPoint c i j hij (pencilScalar e b c i j hij a) := by
  have hi := repr_image_basisPencilPoint_ne_zero e he b c hbc i j hij a
  have h := (mk_coordinateRepresentative c i _ hi).symm
  refine h.trans ?_
  apply (mk_eq_mk_iff' L _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simpa only [one_smul] using
    (coordinateRepresentative_image_basisPencilPoint e he b c hbc i j hij a).symm

/-- The scalar function fixes zero before any further basis normalization. -/
@[simp]
theorem pencilScalar_zero (i j : ι) (hij : i ≠ j) :
    pencilScalar e b c i j hij 0 = 0 := by
  apply basisPencilPoint_injective c i j hij
  rw [← image_basisPencilPoint e he b c hbc, basisPencilPoint_zero,
    basisPencilPoint_zero, hbc]

omit he in
/-- The actual inverse point map is compatible with the same two bases. -/
theorem symm_image_mk_basis (i : ι) :
    e.symm (mk L (c i) (c.ne_zero i)) = mk K (b i) (b.ne_zero i) := by
  rw [← hbc i, e.symm_apply_apply]

/-- Each pencil scalar map is injective, using injectivity of the given point map. -/
theorem pencilScalar_injective (i j : ι) (hij : i ≠ j) :
    Function.Injective (pencilScalar e b c i j hij) := by
  intro a d h
  apply basisPencilPoint_injective b i j hij
  apply e.injective
  rw [image_basisPencilPoint e he b c hbc, image_basisPencilPoint e he b c hbc, h]

/-- Each pencil scalar map is surjective. A parameter is recovered using the
actual inverse projective equivalence, not by assuming a scalar homomorphism. -/
theorem pencilScalar_surjective (i j : ι) (hij : i ≠ j) :
    Function.Surjective (pencilScalar e b c i j hij) := by
  intro a
  let d := pencilScalar e.symm c b i j hij a
  refine ⟨d, ?_⟩
  apply basisPencilPoint_injective c i j hij
  rw [← image_basisPencilPoint e he b c hbc]
  have h := image_basisPencilPoint e.symm (Subspace.finite_span_symm_iff e he)
    c b (symm_image_mk_basis e b c hbc) i j hij a
  exact (congrArg e h).symm.trans (e.apply_symm_apply _)

/-- The scalar bijection supplied by the coordinate pencil. -/
def pencilEquiv (i j : ι) (hij : i ≠ j) : K ≃ L :=
  Equiv.ofBijective (pencilScalar e b c i j hij)
    ⟨pencilScalar_injective e he b c hbc i j hij,
      pencilScalar_surjective e he b c hbc i j hij⟩

/-- The bundled equivalence has the previously defined coordinate function. -/
@[simp]
theorem pencilEquiv_apply (i j : ι) (hij : i ≠ j) (a : K) :
    pencilEquiv e he b c hbc i j hij a = pencilScalar e b c i j hij a := rfl

/-- The inverse is precisely the pencil function of the inverse point map. -/
theorem pencilEquiv_symm_apply (i j : ι) (hij : i ≠ j) (a : L) :
    (pencilEquiv e he b c hbc i j hij).symm a =
      pencilScalar e.symm c b i j hij a := by
  apply (pencilEquiv e he b c hbc i j hij).injective
  rw [Equiv.apply_symm_apply, pencilEquiv_apply]
  apply basisPencilPoint_injective c i j hij
  rw [← image_basisPencilPoint e he b c hbc]
  have h := image_basisPencilPoint e.symm (Subspace.finite_span_symm_iff e he)
    c b (symm_image_mk_basis e b c hbc) i j hij a
  exact (e.apply_symm_apply _).symm.trans (congrArg e h)

/-- Nonzero parameters remain nonzero; in particular the value at `1` can be
used to rescale a basis vector. -/
theorem pencilScalar_ne_zero (i j : ι) (hij : i ≠ j) {a : K} (ha : a ≠ 0) :
    pencilScalar e b c i j hij a ≠ 0 := by
  intro hz
  apply ha
  apply pencilScalar_injective e he b c hbc i j hij
  rw [hz, pencilScalar_zero e he b c hbc]

/-- Units which normalize all pencils through a fixed anchor simultaneously.
The anchor itself is left unchanged. -/
def pencilNormalizationUnits (o : ι) (i : ι) : Lˣ :=
  if h : o = i then 1 else
    Units.mk0 (pencilScalar e b c o i h 1)
      (pencilScalar_ne_zero e he b c hbc o i h one_ne_zero)

/-- The actual normalized target basis, with the same arbitrary index type. -/
def normalizedBasis (o : ι) : Module.Basis ι L W :=
  c.unitsSMul (pencilNormalizationUnits e he b c hbc o)

/-- Evaluation at the anchor. -/
@[simp]
theorem normalizedBasis_anchor (o : ι) :
    normalizedBasis e he b c hbc o o = c o := by
  simp [normalizedBasis, Module.Basis.unitsSMul_apply, pencilNormalizationUnits]

/-- Evaluation away from the anchor uses the nonzero value at parameter one. -/
theorem normalizedBasis_apply (o i : ι) (hoi : o ≠ i) :
    normalizedBasis e he b c hbc o i = pencilScalar e b c o i hoi 1 • c i := by
  simp [normalizedBasis, Module.Basis.unitsSMul_apply, pencilNormalizationUnits,
    hoi, Units.smul_def]

/-- Rescaling leaves all the prescribed basis rays unchanged. -/
theorem image_mk_normalizedBasis (o i : ι) :
    e (mk K (b i) (b.ne_zero i)) =
      mk L (normalizedBasis e he b c hbc o i)
        ((normalizedBasis e he b c hbc o).ne_zero i) := by
  rw [hbc i]
  symm
  apply (mk_eq_mk_iff' L _ _ ((normalizedBasis e he b c hbc o).ne_zero i)
    (c.ne_zero i)).mpr
  refine ⟨(pencilNormalizationUnits e he b c hbc o i : L), ?_⟩
  simp only [normalizedBasis, Module.Basis.unitsSMul_apply, Units.smul_def]

/-- The defining additional normalization is an exact statement about the given
equivalence on every anchor-plus-basis-vector ray. -/
theorem image_basisPencilPoint_one_normalizedBasis (o i : ι) (hoi : o ≠ i) :
    e (basisPencilPoint b o i hoi 1) =
      basisPencilPoint (normalizedBasis e he b c hbc o) o i hoi 1 := by
  rw [image_basisPencilPoint e he b c hbc]
  simp only [basisPencilPoint, one_smul, normalizedBasis_anchor,
    normalizedBasis_apply e he b c hbc o i hoi]

/-- In normalized target coordinates each anchor-pencil bijection fixes one.
This does not yet assert that different pencils induce the same scalar map. -/
theorem pencilScalar_one_normalizedBasis (o i : ι) (hoi : o ≠ i) :
    pencilScalar e b (normalizedBasis e he b c hbc o) o i hoi 1 = 1 := by
  apply basisPencilPoint_injective (normalizedBasis e he b c hbc o) o i hoi
  rw [← image_basisPencilPoint e he b (normalizedBasis e he b c hbc o)
    (image_mk_normalizedBasis e he b c hbc o)]
  exact image_basisPencilPoint_one_normalizedBasis e he b c hbc o i hoi

omit hbc in
/-- No compatible target basis needs to be supplied: the existing transported
basis is normalized using the actual pencil maps of the given equivalence. -/
def normalizedBasisOfFiniteSpan (b : Module.Basis ι K V) (o : ι) : Module.Basis ι L W :=
  normalizedBasis e he b (basisOfFiniteSpan e he b)
    (fun i => (mk_basisOfFiniteSpan e he b i).symm) o

omit hbc in
/-- The canonically chosen normalized basis has the prescribed basis-ray images. -/
theorem image_mk_normalizedBasisOfFiniteSpan (b : Module.Basis ι K V) (o i : ι) :
    e (mk K (b i) (b.ne_zero i)) =
      mk L (normalizedBasisOfFiniteSpan e he b o i)
        ((normalizedBasisOfFiniteSpan e he b o).ne_zero i) :=
  image_mk_normalizedBasis e he b (basisOfFiniteSpan e he b)
    (fun j => (mk_basisOfFiniteSpan e he b j).symm) o i

omit hbc in
/-- Its additional anchor-ray normalization also concerns the specified e. -/
theorem image_basisPencilPoint_one_normalizedBasisOfFiniteSpan
    (b : Module.Basis ι K V) (o i : ι) (hoi : o ≠ i) :
    e (basisPencilPoint b o i hoi 1) =
      basisPencilPoint (normalizedBasisOfFiniteSpan e he b o) o i hoi 1 :=
  image_basisPencilPoint_one_normalizedBasis e he b (basisOfFiniteSpan e he b)
    (fun j => (mk_basisOfFiniteSpan e he b j).symm) o i hoi

omit hbc in
/-- Every anchor pencil in the canonically normalized basis fixes one. -/
theorem pencilScalar_one_normalizedBasisOfFiniteSpan
    (b : Module.Basis ι K V) (o i : ι) (hoi : o ≠ i) :
    pencilScalar e b (normalizedBasisOfFiniteSpan e he b o) o i hoi 1 = 1 :=
  pencilScalar_one_normalizedBasis e he b (basisOfFiniteSpan e he b)
    (fun j => (mk_basisOfFiniteSpan e he b j).symm) o i hoi

omit he hbc in
/-- The algebraic coordinate hyperplane `v_i = a v_o`. No topology is present. -/
def coordinateHyperplane (o i : ι) (a : K) : Submodule K V :=
  LinearMap.ker (b.coord i - a • b.coord o)

omit he hbc in
/-- Membership in the coordinate hyperplane is the stated scalar equation. -/
theorem mem_coordinateHyperplane_iff (o i : ι) (a : K) (v : V) :
    v ∈ coordinateHyperplane b o i a ↔ b.repr v i = a * b.repr v o := by
  change b.repr v i - a * b.repr v o = 0 ↔ _
  exact sub_eq_zero

omit he hbc in
/-- A coordinate hyperplane is generated by one pencil vector and all basis
vectors outside the two chosen indices. Those other indices may be infinite. -/
theorem coordinateHyperplane_eq_sup_span (o i : ι) (hoi : o ≠ i) (a : K) :
    coordinateHyperplane b o i a =
      (K ∙ (b o + a • b i)) ⊔ Submodule.span K (b '' ({o, i} : Set ι)ᶜ) := by
  apply le_antisymm
  · intro v hv
    have hvi := (mem_coordinateHyperplane_iff b o i a v).mp hv
    let w := v - b.repr v o • (b o + a • b i)
    have hw : w ∈ Submodule.span K (b '' ({o, i} : Set ι)ᶜ) := by
      rw [mem_span_basis_image_iff]
      intro k hk
      have hk' : k = o ∨ k = i := by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_not] using hk
      rcases hk' with rfl | rfl
      · simp [w, hoi, hoi.symm]
      · simp [w, hoi, hoi.symm, hvi, mul_comm]
    exact Submodule.mem_sup.mpr
      ⟨b.repr v o • (b o + a • b i),
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), w, hw,
        by simp [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]⟩
  · apply sup_le
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      rw [mem_coordinateHyperplane_iff]
      simp [hoi, hoi.symm]
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      have hjo : j ≠ o := fun h => hj (by simp [h])
      have hji : j ≠ i := fun h => hj (by simp [h])
      change b j ∈ coordinateHyperplane b o i a
      rw [mem_coordinateHyperplane_iff]
      simp [hjo, hji, hjo.symm, hji.symm]

/-- The order map sends each full coordinate hyperplane to the hyperplane whose
parameter is read from the given pencil map. This concerns all vectors. -/
theorem submoduleOrderIsoOfFiniteSpan_coordinateHyperplane
    (o i : ι) (hoi : o ≠ i) (a : K) :
    submoduleOrderIsoOfFiniteSpan e he (coordinateHyperplane b o i a) =
      coordinateHyperplane c o i (pencilScalar e b c o i hoi a) := by
  rw [coordinateHyperplane_eq_sup_span b o i hoi,
    submoduleOrderIsoOfFiniteSpan_sup,
    submoduleOrderIsoOfFiniteSpan_span_singleton e he _
      (basis_add_smul_ne_zero b o i hoi a),
    submoduleOrderIsoOfFiniteSpan_span_basis_image e he b c hbc]
  change (e (basisPencilPoint b o i hoi a)).submodule ⊔ _ = _
  rw [image_basisPencilPoint e he b c hbc]
  change (L ∙ (c o + pencilScalar e b c o i hoi a • c i)) ⊔ _ = _
  exact (coordinateHyperplane_eq_sup_span c o i hoi _).symm

/-- Homogeneous coordinate equations hold on any scalar multiple of an image
representative, including its normalized chart representative. -/
theorem coordinateRepresentative_image_mem_coordinateHyperplane
    (o i j : ι) (hij : i ≠ j) (a : K) (v : V) (hv : v ≠ 0)
    (hP : v ∈ coordinateHyperplane b i j a) :
    coordinateRepresentative c o (e (mk K v hv)) ∈
      coordinateHyperplane c i j (pencilScalar e b c i j hij a) := by
  have hw : (e (mk K v hv)).rep ∈
      submoduleOrderIsoOfFiniteSpan e he (coordinateHyperplane b i j a) := by
    rw [mem_submoduleOrderIsoOfFiniteSpan_iff e he _ _ (rep_nonzero _),
      mk_rep, e.symm_apply_apply, Submodule.mk_mem_projectivization_iff]
    exact hP
  rw [submoduleOrderIsoOfFiniteSpan_coordinateHyperplane e he b c hbc i j hij a] at hw
  exact Submodule.smul_mem _ _ hw

/-- Every coordinate of the normalized image of an arbitrary affine-chart
vector is controlled by its own pencil parameter. No finite-support bound or
finite-dimensionality assumption is needed. -/
theorem repr_coordinateRepresentative_image (o i : ι) (hoi : o ≠ i)
    (v : V) (hv : v ≠ 0) (hvo : b.repr v o = 1) :
    c.repr (coordinateRepresentative c o (e (mk K v hv))) i =
      pencilScalar e b c o i hoi (b.repr v i) := by
  have ho : c.repr (e (mk K v hv)).rep o ≠ 0 := by
    intro hz
    have hzero := (repr_image_rep_eq_zero_iff e he b c hbc v hv o).mp hz
    exact one_ne_zero (hvo.symm.trans hzero)
  have hvP : v ∈ coordinateHyperplane b o i (b.repr v i) := by
    rw [mem_coordinateHyperplane_iff, hvo, mul_one]
  have hwP : (e (mk K v hv)).rep ∈
      submoduleOrderIsoOfFiniteSpan e he (coordinateHyperplane b o i (b.repr v i)) := by
    rw [mem_submoduleOrderIsoOfFiniteSpan_iff e he _ _ (rep_nonzero _),
      mk_rep, e.symm_apply_apply, Submodule.mk_mem_projectivization_iff]
    exact hvP
  have hw := Submodule.smul_mem
    (submoduleOrderIsoOfFiniteSpan e he (coordinateHyperplane b o i (b.repr v i)))
    ((c.repr (e (mk K v hv)).rep o)⁻¹) hwP
  change coordinateRepresentative c o (e (mk K v hv)) ∈ _ at hw
  rw [submoduleOrderIsoOfFiniteSpan_coordinateHyperplane e he b c hbc,
    mem_coordinateHyperplane_iff, repr_coordinateRepresentative_self c o _ ho,
    mul_one] at hw
  exact hw

/-- Formula at every coordinate, including the anchor itself. The vector on the
left realizes the given projective image exactly. -/
theorem repr_coordinateRepresentative_image_eq (o : ι) (v : V) (hv : v ≠ 0)
    (hvo : b.repr v o = 1) (i : ι) :
    c.repr (coordinateRepresentative c o (e (mk K v hv))) i =
      if hoi : o = i then 1 else pencilScalar e b c o i hoi (b.repr v i) := by
  by_cases hoi : o = i
  · subst i
    have ho : c.repr (e (mk K v hv)).rep o ≠ 0 := by
      intro hz
      exact one_ne_zero (hvo.symm.trans
        ((repr_image_rep_eq_zero_iff e he b c hbc v hv o).mp hz))
    simp [repr_coordinateRepresentative_self c o _ ho]
  · simpa only [dif_neg hoi] using
      repr_coordinateRepresentative_image e he b c hbc o i hoi v hv hvo

end Projectivization
