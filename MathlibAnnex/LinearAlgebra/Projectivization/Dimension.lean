/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.LinearAlgebra.Projectivization.SubspaceEquiv
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Generation, independence and dimension under projective incidence

The order map is the one already constructed from the given projective point
bijection. Independence is transported through Mathlib's lattice-theoretic
criterion. A basis is then transported by choosing representatives of its image
points and proving both independence and spanning. This does NOT construct a
semilinear realization of the point map.

Finite generation is proved by induction on finite algebraic generation, not
by silently replacing arbitrary submodules by closed ones. Finite dimensionality
is explicit whenever `finrank` is interpreted as a dimension.
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

include he in
/-- Independence of arbitrary indexed families, hence also of finite families,
is preserved and reflected by finite-span incidence. -/
theorem independent_comp_iff_of_finite_span {ι : Type uI} (p : ι → ℙ K V) :
    Independent (e ∘ p) ↔ Independent p := by
  rw [independent_iff_iSupIndep, independent_iff_iSupIndep]
  have hf : (fun i => (e (p i)).submodule) =
      submoduleOrderIsoOfFiniteSpan e he ∘ (fun i => (p i).submodule) := by
    funext i
    exact (submoduleOrderIsoOfFiniteSpan_submodule e he (p i)).symm
  change iSupIndep (fun i => (e (p i)).submodule) ↔ _
  rw [hf]
  exact iSupIndep_map_orderIso_iff (submoduleOrderIsoOfFiniteSpan e he)

include he in
/-- The same independence statement on Mathlib's nonzero representatives. -/
theorem linearIndependent_rep_comp_iff_of_finite_span {ι : Type uI}
    (p : ι → ℙ K V) :
    LinearIndependent L (fun i => (e (p i)).rep) ↔
      LinearIndependent K (fun i => (p i).rep) := by
  simpa only [independent_iff, Function.comp_def] using
    independent_comp_iff_of_finite_span e he p

/-- Finite generation of a submodule is preserved. The proof treats a zero
new generator separately and otherwise uses the actual image projective line. -/
theorem fg_submoduleOrderIsoOfFiniteSpan (P : Submodule K V) (hP : P.FG) :
    (submoduleOrderIsoOfFiniteSpan e he P).FG := by
  refine Submodule.fg_sup_span_induction
    (motive := fun Q _ => (submoduleOrderIsoOfFiniteSpan e he Q).FG) ?_ ?_ P hP
  · simpa only [submoduleOrderIsoOfFiniteSpan_bot] using
      (Submodule.fg_bot : (⊥ : Submodule L W).FG)
  · intro Q v hQ ih
    rw [submoduleOrderIsoOfFiniteSpan_sup]
    apply ih.sup
    by_cases hv : v = 0
    · subst v
      simpa using (Submodule.fg_bot : (⊥ : Submodule L W).FG)
    · rw [submoduleOrderIsoOfFiniteSpan_span_singleton e he v hv, submodule_eq]
      exact Submodule.fg_span_singleton _

/-- Finite generation is also reflected; the map here acts on all submodules. -/
theorem fg_submoduleOrderIsoOfFiniteSpan_iff (P : Submodule K V) :
    (submoduleOrderIsoOfFiniteSpan e he P).FG ↔ P.FG := by
  refine ⟨?_, fg_submoduleOrderIsoOfFiniteSpan e he P⟩
  intro hP
  have h := fg_submoduleOrderIsoOfFiniteSpan e.symm
    (Subspace.finite_span_symm_iff e he) (submoduleOrderIsoOfFiniteSpan e he P) hP
  rw [← submoduleOrderIsoOfFiniteSpan_symm e he,
    symm_apply_submoduleOrderIsoOfFiniteSpan] at h
  exact h

/-- The points determined by any algebraic basis span the whole projective space.
The empty basis of a zero module is included. -/
theorem span_range_mk_basis_eq_top {ι : Type uI} (b : Module.Basis ι K V) :
    Subspace.span (range fun i => mk K (b i) (b.ne_zero i)) = ⊤ := by
  apply Subspace.submodule.injective
  rw [Subspace.submodule.map_top]
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (Subspace.mem_submodule_iff _ (b.ne_zero i)).mpr
    (Subspace.subset_span _ (mem_range_self i))

include he in
/-- Representatives of the image of a projective spanning family span the
whole target vector space. No assumption on either dimension is made. -/
theorem span_range_rep_comp_eq_top_of_finite_span {ι : Type uI}
    (p : ι → ℙ K V) (hp : Subspace.span (range p) = ⊤) :
    Submodule.span L (range fun i => (e (p i)).rep) = ⊤ := by
  have hspan : Subspace.span (e '' range p) = ⊤ := by
    rw [← Subspace.orderIsoOfFiniteSpan_span e he, hp]
    exact (Subspace.orderIsoOfFiniteSpan e he).map_top
  have hrange : Projectivization.rep '' (e '' range p) =
      range (fun i => (e (p i)).rep) := by
    ext w
    constructor
    · rintro ⟨q, ⟨r, ⟨i, rfl⟩, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e (p i), ⟨p i, mem_range_self i, rfl⟩, rfl⟩
  rw [← hrange, ← Subspace.submodule_span_eq_span_rep_image, hspan,
    Subspace.submodule.map_top]

/-- A basis of the source gives an actual basis of the target with the same
index type. This is a choice of image representatives, not a semilinear lift. -/
def basisOfFiniteSpan {ι : Type uI} (b : Module.Basis ι K V) : Module.Basis ι L W := by
  let p : ι → ℙ K V := fun i => mk K (b i) (b.ne_zero i)
  have hp : Independent p := Independent.mk b b.ne_zero b.linearIndependent
  have heP : Independent (e ∘ p) :=
    (independent_comp_iff_of_finite_span e he p).mpr hp
  have hlin : LinearIndependent L (fun i => (e (p i)).rep) :=
    independent_iff.mp heP
  have hspan : Submodule.span L (range fun i => (e (p i)).rep) = ⊤ :=
    span_range_rep_comp_eq_top_of_finite_span e he p (span_range_mk_basis_eq_top b)
  exact Module.Basis.mk hlin hspan.ge

/-- The transported basis has exactly the chosen representative at each index. -/
@[simp]
theorem basisOfFiniteSpan_apply {ι : Type uI} (b : Module.Basis ι K V) (i : ι) :
    basisOfFiniteSpan e he b i = (e (mk K (b i) (b.ne_zero i))).rep := by
  unfold basisOfFiniteSpan
  rw [Module.Basis.mk_apply]

/-- The basis realizes the given projective images on its basis vectors only. -/
@[simp]
theorem mk_basisOfFiniteSpan {ι : Type uI} (b : Module.Basis ι K V) (i : ι) :
    mk L (basisOfFiniteSpan e he b i) ((basisOfFiniteSpan e he b).ne_zero i) =
      e (mk K (b i) (b.ne_zero i)) := by
  simpa only [basisOfFiniteSpan_apply] using
    (mk_rep (e (mk K (b i) (b.ne_zero i))))

include e he in
/-- If the source is finite dimensional, the target really is finite dimensional. -/
theorem finite_of_finite_span [Module.Finite K V] : Module.Finite L W :=
  Module.Finite.of_basis (basisOfFiniteSpan e he (Module.finBasis K V))

include e he in
/-- Finite dimensionality is equivalent, including the zero-dimensional case. -/
theorem finite_iff_of_finite_span : Module.Finite K V ↔ Module.Finite L W := by
  constructor
  · intro hV
    letI : Module.Finite K V := hV
    exact finite_of_finite_span e he
  · intro hW
    letI : Module.Finite L W := hW
    exact finite_of_finite_span e.symm (Subspace.finite_span_symm_iff e he)

include e he in
/-- Dimension equality with an actual finite-dimensional hypothesis. In an
infinite-dimensional space `finrank = 0` is not used to infer triviality. -/
theorem finrank_eq_of_finite_span [Module.Finite K V] :
    Module.finrank K V = Module.finrank L W := by
  have h := Module.finrank_eq_card_basis
    (basisOfFiniteSpan e he (Module.finBasis K V))
  simpa only [Fintype.card_fin] using h.symm

include e he in
/-- Either finite-dimensionality hypothesis suffices, without privileging a side. -/
theorem finite_and_finrank_eq_of_finite_span
    (hfinite : Module.Finite K V ∨ Module.Finite L W) :
    Module.Finite K V ∧ Module.Finite L W ∧
      Module.finrank K V = Module.finrank L W := by
  have hV : Module.Finite K V := hfinite.elim id (finite_iff_of_finite_span e he).mpr
  letI : Module.Finite K V := hV
  exact ⟨hV, finite_of_finite_span e he, finrank_eq_of_finite_span e he⟩

end Projectivization
