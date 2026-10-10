/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.LinearAlgebra.Projectivization.CoordinateLift
import MathlibAnnex.LinearAlgebra.Basis.Semilinear
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Semilinear realization from finite projective incidence

The normalized pencil equivalences are synchronized by three-coordinate
incidence. Multiplication and the identity `σ (1 - t) = 1 - σ t` are then derived
from actual subspace transport; together with bijectivity these imply addition.
No scalar regularity or linear realization of the point map is assumed.

The resulting scalar ring isomorphism acts on finitely supported basis
coefficients to construct a semilinear equivalence. Affine-chart agreement is
proved coordinate by coordinate; the anchor-zero case is proved separately by
intersecting a two-dimensional span with the coordinate hyperplane. The final
existence theorem assumes only algebraic rank at least three, over fields.
The imported DivisionRing results are unchanged; this new coordinate realization
does not assert the noncommutative DivisionRing extension.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

universe uK uL uV uW uI
variable {K : Type uK} {L : Type uL} {V : Type uV} {W : Type uW}
variable [Field K] [Field L]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
variable {ι : Type uI}

local instance (σ : K ≃+* L) : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ
local instance (σ : K ≃+* L) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-- The affine coordinate plane has nonzero anchor coordinate, including when
one or both variable coefficients are zero. -/
theorem basis_add_smul_add_smul_ne_zero (b : Module.Basis ι K V)
    (o i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (a d : K) :
    b o + a • b i + d • b j ≠ 0 := by
  intro h
  have hc := congrArg (fun v : V => b.repr v o) h
  simpa [hoi, hoj, hoi.symm, hoj.symm] using hc

/-- A point in the actual three-coordinate projective plane. -/
def basisPlanePoint (b : Module.Basis ι K V)
    (o i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (a d : K) : ℙ K V :=
  mk K (b o + a • b i + d • b j)
    (basis_add_smul_add_smul_ne_zero b o i j hoi hoj a d)

section ScalarRigidity

variable (e : ℙ K V ≃ ℙ L W)
variable (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
  p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
variable (b : Module.Basis ι K V) (c : Module.Basis ι L W)
variable (hbc : ∀ i, e (mk K (b i) (b.ne_zero i)) = mk L (c i) (c.ne_zero i))
include he hbc

/-- The two variable coordinates of a normalized image are read from the two
anchor pencils, without assuming those two scalar maps agree. -/
theorem repr_coordinateRepresentative_image_basisPlanePoint
    (o i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (a d : K) :
    c.repr (coordinateRepresentative c o (e (basisPlanePoint b o i j hoi hoj a d))) i =
        pencilScalar e b c o i hoi a ∧
      c.repr (coordinateRepresentative c o (e (basisPlanePoint b o i j hoi hoj a d))) j =
        pencilScalar e b c o j hoj d := by
  have hv := basis_add_smul_add_smul_ne_zero b o i j hoi hoj a d
  have ho : b.repr (b o + a • b i + d • b j) o = 1 := by
    simp [hoi, hoj, hoi.symm, hoj.symm]
  constructor
  · simpa [basisPlanePoint, hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm] using
      repr_coordinateRepresentative_image e he b c hbc o i hoi _ hv ho
  · simpa [basisPlanePoint, hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm] using
      repr_coordinateRepresentative_image e he b c hbc o j hoj _ hv ho

variable (o : ι)
variable (h1 : ∀ i (hoi : o ≠ i), pencilScalar e b c o i hoi 1 = 1)
include h1

/-- A pencil between two nonanchor axes has the same parameter map as the
anchor pencil ending at its second axis. A point with first coordinate one
provides the equality of parameters. -/
theorem pencilScalar_eq_anchor (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (a : K) :
    pencilScalar e b c i j hij a = pencilScalar e b c o j hoj a := by
  have hv := basis_add_smul_add_smul_ne_zero b o i j hoi hoj 1 a
  have hvP : b o + (1 : K) • b i + a • b j ∈ coordinateHyperplane b i j a := by
    rw [mem_coordinateHyperplane_iff]
    simp [hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm]
  have hP := coordinateRepresentative_image_mem_coordinateHyperplane e he b c hbc
    o i j hij a _ hv hvP
  rw [mem_coordinateHyperplane_iff] at hP
  have hc := repr_coordinateRepresentative_image_basisPlanePoint e he b c hbc
    o i j hoi hoj hij 1 a
  change c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj 1 a))) j =
    pencilScalar e b c i j hij a * c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj 1 a))) i at hP
  rw [hc.1, hc.2, h1 i hoi, mul_one] at hP
  exact hP.symm

/-- All normalized anchor pencils agree pairwise. Distinctness is required only
for the three axes used in this proof, not for the ambient basis as a finite set. -/
theorem pencilScalar_eq_of_normalized (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (a : K) :
    pencilScalar e b c o i hoi a = pencilScalar e b c o j hoj a := by
  have hv := basis_add_smul_add_smul_ne_zero b o i j hoi hoj a a
  have hvP : b o + a • b i + a • b j ∈ coordinateHyperplane b i j 1 := by
    rw [mem_coordinateHyperplane_iff]
    simp [hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm]
  have hP := coordinateRepresentative_image_mem_coordinateHyperplane e he b c hbc
    o i j hij 1 _ hv hvP
  rw [mem_coordinateHyperplane_iff] at hP
  have hc := repr_coordinateRepresentative_image_basisPlanePoint e he b c hbc
    o i j hoi hoj hij a a
  change c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj a a))) j =
    pencilScalar e b c i j hij 1 * c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj a a))) i at hP
  rw [hc.1, hc.2, pencilScalar_eq_anchor e he b c hbc o h1 i j hoi hoj hij,
    h1 j hoj, one_mul] at hP
  exact hP.symm

/-- Multiplication comes from the homogeneous equation `v_j = a v_i` in an
actual three-coordinate plane. No multiplication law is supplied as an input. -/
theorem pencilScalar_mul_of_normalized (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (a t : K) :
    pencilScalar e b c o j hoj (a * t) =
      pencilScalar e b c o j hoj a * pencilScalar e b c o j hoj t := by
  have hv := basis_add_smul_add_smul_ne_zero b o i j hoi hoj t (a * t)
  have hvP : b o + t • b i + (a * t) • b j ∈ coordinateHyperplane b i j a := by
    rw [mem_coordinateHyperplane_iff]
    simp [hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm]
  have hP := coordinateRepresentative_image_mem_coordinateHyperplane e he b c hbc
    o i j hij a _ hv hvP
  rw [mem_coordinateHyperplane_iff] at hP
  have hc := repr_coordinateRepresentative_image_basisPlanePoint e he b c hbc
    o i j hoi hoj hij t (a * t)
  change c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj t (a * t)))) j =
    pencilScalar e b c i j hij a * c.repr (coordinateRepresentative c o
      (e (basisPlanePoint b o i j hoi hoj t (a * t)))) i at hP
  rw [hc.1, hc.2, pencilScalar_eq_anchor e he b c hbc o h1 i j hoi hoj hij,
    pencilScalar_eq_of_normalized e he b c hbc o h1 i j hoi hoj hij] at hP
  exact hP

/-- The affine line joining the normalized unit points gives preservation of
`1 - t`. Its target equation is derived from two actual image lines. -/
theorem pencilScalar_one_sub_of_normalized (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (t : K) :
    pencilScalar e b c o j hoj (1 - t) = 1 - pencilScalar e b c o j hoj t := by
  let x := b o + b i
  let y := b o + b j
  let v := b o + t • b i + (1 - t) • b j
  have hx : x ≠ 0 := by simpa [x] using basis_add_smul_ne_zero b o i hoi (1 : K)
  have hy : y ≠ 0 := by simpa [y] using basis_add_smul_ne_zero b o j hoj (1 : K)
  have hv : v ≠ 0 := basis_add_smul_add_smul_ne_zero b o i j hoi hoj t (1 - t)
  let P : Submodule K V := (K ∙ x) ⊔ (K ∙ y)
  have hxP : x ∈ P := (show K ∙ x ≤ P from le_sup_left) (Submodule.mem_span_singleton_self x)
  have hyP : y ∈ P := (show K ∙ y ≤ P from le_sup_right) (Submodule.mem_span_singleton_self y)
  have hvP : v ∈ P := by
    have hs := P.add_mem (P.smul_mem t hxP) (P.smul_mem (1 - t) hyP)
    have heq : t • x + (1 - t) • y = v := by
      dsimp [x, y, v]
      simp only [smul_add, sub_smul, one_smul]
      abel
    exact heq ▸ hs
  have hpx : mk K x hx = basisPencilPoint b o i hoi 1 := by simp [x, basisPencilPoint]
  have hpy : mk K y hy = basisPencilPoint b o j hoj 1 := by simp [y, basisPencilPoint]
  have hmap : submoduleOrderIsoOfFiniteSpan e he P =
      (L ∙ (c o + c i)) ⊔ (L ∙ (c o + c j)) := by
    dsimp [P]
    rw [submoduleOrderIsoOfFiniteSpan_sup,
      submoduleOrderIsoOfFiniteSpan_span_singleton e he x hx,
      submoduleOrderIsoOfFiniteSpan_span_singleton e he y hy,
      hpx, hpy, image_basisPencilPoint e he b c hbc,
      image_basisPencilPoint e he b c hbc, h1 i hoi, h1 j hoj]
    simp only [basisPencilPoint, submodule_mk, one_smul]
  let M : Submodule L W := LinearMap.ker (c.coord i + c.coord j - c.coord o)
  have hPM : submoduleOrderIsoOfFiniteSpan e he P ≤ M := by
    rw [hmap]
    apply sup_le
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      change c.repr (c o + c i) i + c.repr (c o + c i) j - c.repr (c o + c i) o = 0
      simp [hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm]
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      change c.repr (c o + c j) i + c.repr (c o + c j) j - c.repr (c o + c j) o = 0
      simp [hoi, hoj, hij, hoi.symm, hoj.symm, hij.symm]
  have hwP : (e (mk K v hv)).rep ∈ submoduleOrderIsoOfFiniteSpan e he P := by
    rw [mem_submoduleOrderIsoOfFiniteSpan_iff e he _ _ (rep_nonzero _),
      mk_rep, e.symm_apply_apply, Submodule.mk_mem_projectivization_iff]
    exact hvP
  have hw := hPM ((submoduleOrderIsoOfFiniteSpan e he P).smul_mem
    ((c.repr (e (mk K v hv)).rep o)⁻¹) hwP)
  change c.repr (coordinateRepresentative c o (e (mk K v hv))) i +
    c.repr (coordinateRepresentative c o (e (mk K v hv))) j -
    c.repr (coordinateRepresentative c o (e (mk K v hv))) o = 0 at hw
  have ho : c.repr (e (mk K v hv)).rep o ≠ 0 := by
    intro hz
    have hz' := (repr_image_rep_eq_zero_iff e he b c hbc v hv o).mp hz
    simpa [v, hoi, hoj, hoi.symm, hoj.symm] using hz'
  have hc := repr_coordinateRepresentative_image_basisPlanePoint e he b c hbc
    o i j hoi hoj hij t (1 - t)
  change c.repr (coordinateRepresentative c o (e (mk K v hv))) i = _ ∧
    c.repr (coordinateRepresentative c o (e (mk K v hv))) j = _ at hc
  rw [hc.1, hc.2, repr_coordinateRepresentative_self c o _ ho,
    pencilScalar_eq_of_normalized e he b c hbc o h1 i j hoi hoj hij] at hw
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_zero.mp hw)

omit he hbc h1 in
private theorem add_of_mul_one_sub (s : K ≃ L)
    (h0 : s 0 = 0) (h1s : s 1 = 1)
    (hm : ∀ a d, s (a * d) = s a * s d)
    (hs : ∀ a, s (1 - a) = 1 - s a) :
    ∀ a d, s (a + d) = s a + s d := by
  have hne : ∀ a d, a + d ≠ 0 → s (a + d) = s a + s d := by
    intro a d had
    have ha : (a + d) * (a / (a + d)) = a := by field_simp [had] <;> ring
    have hd : (a + d) * (1 - a / (a + d)) = d := by field_simp [had] <;> ring
    calc
      s (a + d) = s (a + d) * s (a / (a + d)) +
          s (a + d) * s (1 - a / (a + d)) := by rw [hs]; ring
      _ = s ((a + d) * (a / (a + d))) +
          s ((a + d) * (1 - a / (a + d))) := by rw [hm, hm]
      _ = s a + s d := by rw [ha, hd]
  intro a d
  by_cases had : a + d = 0
  · obtain ⟨z, hz⟩ := s.surjective (-s a)
    have haz : a + z = 0 := by
      by_contra hn
      have hsaz := hne a z hn
      have heq : s (a + z) = s 0 := by simpa only [hz, add_neg_cancel, h0] using hsaz
      exact hn (s.injective heq)
    have hdz : d = z := add_left_cancel (had.trans haz.symm)
    rw [had, h0, hdz, hz, add_neg_cancel]
  · exact hne a d had

/-- Addition is a consequence of three-coordinate incidence and the already
proved bijection/multiplication/complement laws, in every characteristic. -/
theorem pencilScalar_add_of_normalized (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) (a d : K) :
    pencilScalar e b c o j hoj (a + d) =
      pencilScalar e b c o j hoj a + pencilScalar e b c o j hoj d := by
  exact add_of_mul_one_sub (pencilEquiv e he b c hbc o j hoj)
    (pencilScalar_zero e he b c hbc o j hoj) (h1 j hoj)
    (pencilScalar_mul_of_normalized e he b c hbc o h1 i j hoi hoj hij)
    (pencilScalar_one_sub_of_normalized e he b c hbc o h1 i j hoi hoj hij) a d

/-- The actual scalar isomorphism read from the given projective equivalence.
The only geometric hypotheses beyond finite incidence are the three distinct
axes and a target basis whose anchor pencils have been normalized. -/
def scalarRingEquiv (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j) : K ≃+* L :=
  { pencilEquiv e he b c hbc o j hoj with
    map_mul' := pencilScalar_mul_of_normalized e he b c hbc o h1 i j hoi hoj hij
    map_add' := pencilScalar_add_of_normalized e he b c hbc o h1 i j hoi hoj hij }

/-- Exact evaluation of the scalar isomorphism, not merely its existence. -/
@[simp]
theorem scalarRingEquiv_apply (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j)
    (hij : i ≠ j) (a : K) :
    scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij a =
      pencilScalar e b c o j hoj a := rfl

/-- Every other anchor pencil has this same scalar map, including the case
where the compared axis is the selected reference axis. -/
theorem pencilScalar_eq_scalarRingEquiv (i j : ι)
    (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (k : ι) (hok : o ≠ k) (a : K) :
    pencilScalar e b c o k hok a = scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij a := by
  by_cases hkj : k = j
  · subst k
    rfl
  · exact pencilScalar_eq_of_normalized e he b c hbc o h1 k j hok hoj hkj a

end ScalarRigidity

section Realization

variable (e : ℙ K V ≃ ℙ L W)
variable (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
  p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
variable (b : Module.Basis ι K V) (c : Module.Basis ι L W)
variable (hbc : ∀ i, e (mk K (b i) (b.ne_zero i)) = mk L (c i) (c.ne_zero i))
variable (o : ι)
variable (h1 : ∀ i (hoi : o ≠ i), pencilScalar e b c o i hoi 1 = 1)
include he hbc h1

/-- On the entire affine chart, the semilinear vector equals the normalized
representative of the specified projective image. -/
theorem coordinateRepresentative_image_eq_semilinearEquiv
    (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (v : V) (hv : v ≠ 0) (hvo : b.repr v o = 1) :
    coordinateRepresentative c o (e (mk K v hv)) =
      Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij) v := by
  apply c.repr.injective
  ext k
  rw [Module.Basis.repr_semilinearEquiv]
  by_cases hok : o = k
  · subst k
    have ho : c.repr (e (mk K v hv)).rep o ≠ 0 := by
      intro hz
      exact one_ne_zero (hvo.symm.trans
        ((repr_image_rep_eq_zero_iff e he b c hbc v hv o).mp hz))
    rw [repr_coordinateRepresentative_self c o _ ho, hvo, map_one]
  · rw [repr_coordinateRepresentative_image e he b c hbc o k hok v hv hvo]
    exact pencilScalar_eq_scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij k hok _

/-- Exact ray evaluation when the anchor coordinate is one. -/
theorem image_mk_eq_semilinearEquiv_of_repr_eq_one
    (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (v : V) (hv : v ≠ 0) (hvo : b.repr v o = 1) :
    e (mk K v hv) =
      mk L (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij) v)
        (by simpa only [map_zero] using
          (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij)).injective.ne hv) := by
  have ho : c.repr (e (mk K v hv)).rep o ≠ 0 := by
    intro hz
    exact one_ne_zero (hvo.symm.trans
      ((repr_image_rep_eq_zero_iff e he b c hbc v hv o).mp hz))
  have h := (mk_coordinateRepresentative c o (e (mk K v hv)) ho).symm
  simpa only [coordinateRepresentative_image_eq_semilinearEquiv
    e he b c hbc o h1 i j hoi hoj hij v hv hvo] using h

/-- Rescaling extends the affine-chart evaluation to every vector with nonzero
anchor coordinate. The rescaling is not assumed to fix the given point map. -/
theorem image_mk_eq_semilinearEquiv_of_repr_ne_zero
    (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (v : V) (hv : v ≠ 0) (hvo : b.repr v o ≠ 0) :
    e (mk K v hv) =
      mk L (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij) v)
        (by simpa only [map_zero] using
          (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij)).injective.ne hv) := by
  let σ := scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij
  let U := Module.Basis.semilinearEquiv b c σ
  let v' := (b.repr v o)⁻¹ • v
  have hv' : v' ≠ 0 := smul_ne_zero (inv_ne_zero hvo) hv
  have hvo' : b.repr v' o = 1 := by simp [v', hvo]
  have hr : mk K v' hv' = mk K v hv :=
    (mk_eq_mk_iff' K v' v hv' hv).mpr ⟨(b.repr v o)⁻¹, rfl⟩
  have hu : U v ≠ 0 := by simpa only [map_zero] using U.injective.ne hv
  have hu' : U v' ≠ 0 := by simpa only [map_zero] using U.injective.ne hv'
  have hrU : mk L (U v') hu' = mk L (U v) hu := by
    apply (mk_eq_mk_iff' L _ _ hu' hu).mpr
    exact ⟨σ ((b.repr v o)⁻¹), (U.map_smulₛₗ _ v).symm⟩
  exact (congrArg e hr).symm.trans
    ((image_mk_eq_semilinearEquiv_of_repr_eq_one
      e he b c hbc o h1 i j hoi hoj hij v' hv' hvo').trans hrU)

/-- Exact evaluation at every nonzero vector, including those on the omitted
hyperplane. In the zero-anchor case, the image ray lies in the line spanned by
the image of `b o + v` and the anchor, and its anchor coordinate vanishes. -/
theorem image_mk_eq_semilinearEquiv
    (i j : ι) (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (v : V) (hv : v ≠ 0) :
    e (mk K v hv) =
      mk L (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij) v)
        (by simpa only [map_zero] using
          (Module.Basis.semilinearEquiv b c (scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij)).injective.ne hv) := by
  by_cases hvo : b.repr v o = 0
  · let σ := scalarRingEquiv e he b c hbc o h1 i j hoi hoj hij
    let U := Module.Basis.semilinearEquiv b c σ
    let z := b o + v
    have hzo : b.repr z o = 1 := by simp [z, hvo]
    have hz : z ≠ 0 := by
      intro hz
      have hc := congrArg (fun v : V => b.repr v o) hz
      have h10 : (1 : K) = 0 := by
        simpa only [hzo, map_zero, Finsupp.zero_apply] using hc
      exact one_ne_zero h10
    have huv : U v ≠ 0 := by simpa only [map_zero] using U.injective.ne hv
    have huz : U z ≠ 0 := by simpa only [map_zero] using U.injective.ne hz
    have hez : e (mk K z hz) = mk L (U z) huz :=
      image_mk_eq_semilinearEquiv_of_repr_eq_one
        e he b c hbc o h1 i j hoi hoj hij z hz hzo
    let P : Submodule K V := (K ∙ b o) ⊔ (K ∙ z)
    have hboP : b o ∈ P := (show K ∙ b o ≤ P from le_sup_left)
      (Submodule.mem_span_singleton_self _)
    have hzP : z ∈ P := (show K ∙ z ≤ P from le_sup_right)
      (Submodule.mem_span_singleton_self _)
    have hvP : v ∈ P := by
      have h := P.sub_mem hzP hboP
      simpa [z, add_sub_cancel_left] using h
    have hmap : submoduleOrderIsoOfFiniteSpan e he P =
        (L ∙ c o) ⊔ (L ∙ U z) := by
      dsimp [P]
      rw [submoduleOrderIsoOfFiniteSpan_sup,
        submoduleOrderIsoOfFiniteSpan_span_singleton e he _ (b.ne_zero o),
        submoduleOrderIsoOfFiniteSpan_span_singleton e he _ hz,
        hbc o, hez, submodule_mk, submodule_mk]
      rfl
    have hwP : (e (mk K v hv)).rep ∈ (L ∙ c o) ⊔ (L ∙ U z) := by
      rw [← hmap, mem_submoduleOrderIsoOfFiniteSpan_iff e he _ _ (rep_nonzero _),
        mk_rep, e.symm_apply_apply, Submodule.mk_mem_projectivization_iff]
      exact hvP
    obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := Submodule.mem_sup.mp hwP
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw₁
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw₂
    have hwo : c.repr (e (mk K v hv)).rep o = 0 :=
      (repr_image_rep_eq_zero_iff e he b c hbc v hv o).mpr hvo
    have huzo : c.repr (U z) o = 1 := by
      change c.repr (Module.Basis.semilinearEquiv b c σ z) o = 1
      rw [Module.Basis.repr_semilinearEquiv, hzo, map_one]
    have had : a + d = 0 := by
      have hc := congrArg (fun w : W => c.repr w o) hw
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hc
      rw [huzo, hwo] at hc
      simpa using hc
    have huzv : U z = c o + U v := by
      change Module.Basis.semilinearEquiv b c σ (b o + v) = c o + U v
      rw [map_add, Module.Basis.semilinearEquiv_apply_basis]
    have hd : d • U v = (e (mk K v hv)).rep := by
      calc
        d • U v = (a + d) • c o + d • U v := by rw [had, zero_smul, zero_add]
        _ = a • c o + d • U z := by rw [huzv, smul_add, add_smul]; abel
        _ = (e (mk K v hv)).rep := hw
    exact (mk_rep (e (mk K v hv))).symm.trans
      ((mk_eq_mk_iff' L _ _ (rep_nonzero _) huv).mpr ⟨d, hd⟩)
  · exact image_mk_eq_semilinearEquiv_of_repr_ne_zero
      e he b c hbc o h1 i j hoi hoj hij v hv hvo

end Realization

section CanonicalRealization

variable (e : ℙ K V ≃ ℙ L W)
variable (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
  p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
variable (b : Module.Basis ι K V) (o i j : ι)
variable (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)

/-- The scalar isomorphism constructed from a given point equivalence and three
basis indices. The compatible normalized target basis is constructed, not assumed. -/
def scalarEquivOfFiniteSpan : K ≃+* L :=
  scalarRingEquiv e he b (normalizedBasisOfFiniteSpan e he b o)
    (image_mk_normalizedBasisOfFiniteSpan e he b o) o
    (pencilScalar_one_normalizedBasisOfFiniteSpan e he b o) i j hoi hoj hij

/-- The actual semilinear equivalence realizing the specified projective map.
Its coefficients are the scalar isomorphism just constructed from incidence. -/
def semilinearEquivOfFiniteSpan :
    V ≃ₛₗ[(scalarEquivOfFiniteSpan e he b o i j hoi hoj hij).toRingHom] W :=
  Module.Basis.semilinearEquiv b (normalizedBasisOfFiniteSpan e he b o)
    (scalarEquivOfFiniteSpan e he b o i j hoi hoj hij)

/-- Exact all-ray realization, including vectors whose anchor coordinate is zero. -/
theorem image_mk_eq_semilinearEquivOfFiniteSpan (v : V) (hv : v ≠ 0) :
    e (mk K v hv) = mk L (semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij v)
      (by simpa only [map_zero] using
        (semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij).injective.ne hv) :=
  image_mk_eq_semilinearEquiv e he b (normalizedBasisOfFiniteSpan e he b o)
    (image_mk_normalizedBasisOfFiniteSpan e he b o) o
    (pencilScalar_one_normalizedBasisOfFiniteSpan e he b o) i j hoi hoj hij v hv

/-- Membership in the transported algebraic submodule is evaluated by the
actual inverse semilinear equivalence. The zero vector is treated separately. -/
theorem mem_submoduleOrderIsoOfFiniteSpan_iff_semilinearEquivOfFiniteSpan
    (P : Submodule K V) (w : W) :
    w ∈ submoduleOrderIsoOfFiniteSpan e he P ↔
      (semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij).symm w ∈ P := by
  let U := semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij
  by_cases hw : w = 0
  · subst w
    simp only [map_zero, Submodule.zero_mem, iff_self]
  · have hv : U.symm w ≠ 0 := by simpa only [map_zero] using U.symm.injective.ne hw
    have hr : e (mk K (U.symm w) hv) = mk L w hw := by
      have h := image_mk_eq_semilinearEquivOfFiniteSpan
        e he b o i j hoi hoj hij (U.symm w) hv
      exact h.trans ((mk_eq_mk_iff' L _ _ _ hw).mpr
        ⟨1, by rw [one_smul]; exact (U.apply_symm_apply w).symm⟩)
    have hr' : e.symm (mk L w hw) = mk K (U.symm w) hv := by
      rw [← hr, e.symm_apply_apply]
    rw [mem_submoduleOrderIsoOfFiniteSpan_iff e he P w hw, hr',
      Submodule.mk_mem_projectivization_iff]

/-- Evaluation on every algebraic submodule, without replacing it by its
closure or by a finite-dimensional subspace. -/
theorem submoduleOrderIsoOfFiniteSpan_eq_map_semilinearEquivOfFiniteSpan
    (P : Submodule K V) :
    submoduleOrderIsoOfFiniteSpan e he P =
      P.map (semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij).toLinearMap := by
  let U := semilinearEquivOfFiniteSpan e he b o i j hoi hoj hij
  ext w
  rw [mem_submoduleOrderIsoOfFiniteSpan_iff_semilinearEquivOfFiniteSpan
    e he b o i j hoi hoj hij]
  constructor
  · intro hw
    exact Submodule.mem_map.mpr ⟨U.symm w, hw, U.apply_symm_apply w⟩
  · rintro ⟨v, hv, rfl⟩
    change U.symm (U v) ∈ P
    rwa [U.symm_apply_apply]

end CanonicalRealization

/-- Fundamental semilinear realization over fields. The dimension hypothesis is
cardinal-valued algebraic rank. There is no finite-dimensionality, topology,
regularity, involutivity, or continuity hypothesis on the scalar isomorphism.
The conclusion realizes the given equivalence on every nonzero vector. -/
theorem exists_semilinearEquiv_of_finite_span
    (e : ℙ K V ≃ ℙ L W)
    (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
    (hdim : 3 ≤ Module.rank K V) :
    ∃ σ : K ≃+* L, ∃ U : V ≃ₛₗ[σ.toRingHom] W,
      ∀ (v : V) (hv : v ≠ 0), e (mk K v hv) =
        mk L (U v) (by simpa only [map_zero] using U.injective.ne hv) := by
  classical
  let b := Module.Free.chooseBasis K V
  have hcard : (3 : Cardinal) ≤ Cardinal.mk (Module.Free.ChooseBasisIndex K V) := by
    simpa only [Module.Free.rank_eq_card_chooseBasisIndex] using hdim
  obtain ⟨k⟩ : Nonempty (Fin 3 ↪ Module.Free.ChooseBasisIndex K V) :=
    Cardinal.lift_mk_le'.mp (by simpa using hcard)
  have h01 : k 0 ≠ k 1 := k.injective.ne (by decide)
  have h02 : k 0 ≠ k 2 := k.injective.ne (by decide)
  have h12 : k 1 ≠ k 2 := k.injective.ne (by decide)
  refine ⟨scalarEquivOfFiniteSpan e he b (k 0) (k 1) (k 2) h01 h02 h12,
    semilinearEquivOfFiniteSpan e he b (k 0) (k 1) (k 2) h01 h02 h12, ?_⟩
  exact image_mk_eq_semilinearEquivOfFiniteSpan e he b (k 0) (k 1) (k 2) h01 h02 h12

/-- The same realization as equality of functions on the full projective space.
This is stronger than agreement merely on chosen basis rays. -/
theorem exists_map_eq_of_finite_span
    (e : ℙ K V ≃ ℙ L W)
    (he : ∀ (T : Set (ℙ K V)), T.Finite → ∀ p,
      p ∈ Subspace.span T ↔ e p ∈ Subspace.span (e '' T))
    (hdim : 3 ≤ Module.rank K V) :
    ∃ σ : K ≃+* L, ∃ U : V ≃ₛₗ[σ.toRingHom] W,
      Projectivization.map U.toLinearMap U.injective = e := by
  obtain ⟨σ, U, hU⟩ := exists_semilinearEquiv_of_finite_span e he hdim
  refine ⟨σ, U, ?_⟩
  funext p
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.map_mk]
    exact (hU v hv).symm

end Projectivization
