/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.CAR.Completion
import MathlibAnnex.Analysis.CStarAlgebra.Quotient.Image
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Constructions

/-!
# Completing compatible finite CAR quotients

The source algebra is the actual norm closure of an increasing union of
non-unital star subalgebras of the original algebra. A compatible family of
finite-stage quotients determines a map on the union, and its norm estimate
extends that map to the closure. Multiplication and star are proved by density.
Surjectivity uses both finite-stage surjectivity and closedness of the C*-image.

This is the analytic completion step. Its finite-stage quotients and their
compatibility are explicit inputs; this file does not assert their existence
in an arbitrary antiliminal algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {A : Type u} {B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A contractive non-unital star hom on an actual subalgebra extends to its
norm closure. The inherited norm is used throughout; completeness of the
original, possibly nonclosed subalgebra is not assumed. -/
theorem exists_starAlgHom_extension_topologicalClosure
    (S : NonUnitalStarSubalgebra ℂ A) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x : S, ‖f x‖ ≤ ‖x‖) :
    ∃ g : S.topologicalClosure →⋆ₙₐ[ℂ] B,
      (∀ x : S, g (NonUnitalStarSubalgebra.inclusion S.le_topologicalClosure x) = f x) ∧
      (∀ x : S.topologicalClosure, ‖g x‖ ≤ ‖x‖) := by
  letI : IsClosed (S.topologicalClosure : Set A) := S.isClosed_topologicalClosure
  let i : S →⋆ₙₐ[ℂ] S.topologicalClosure :=
    NonUnitalStarSubalgebra.inclusion S.le_topologicalClosure
  let e : S →ₗ[ℂ] S.topologicalClosure :=
    { toFun := i, map_add' := map_add i, map_smul' := map_smul i }
  let fₗ : S →ₗ[ℂ] B :=
    { toFun := f, map_add' := map_add f, map_smul' := map_smul f }
  have hd : DenseRange e := by
    change DenseRange (Set.inclusion
      (S.le_topologicalClosure : (S : Set A) ⊆ (S.topologicalClosure : Set A)))
    exact (denseRange_inclusion_iff _).2 subset_rfl
  have hnorm : ∀ x : S, ‖fₗ x‖ ≤ (1 : ℝ) * ‖e x‖ := by
    intro x
    rw [one_mul]
    exact hf x
  let F : S.topologicalClosure →L[ℂ] B := fₗ.extendOfNorm e
  have heq (x : S) : F (i x) = f x :=
    LinearMap.extendOfNorm_eq hd ⟨1, hnorm⟩ x
  have hF_norm (x : S.topologicalClosure) : ‖F x‖ ≤ ‖x‖ := by
    simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le hd 1 hnorm x
  have hstar (x : S.topologicalClosure) : F (star x) = star (F x) := by
    refine hd.induction ?_ (isClosed_eq (F.continuous.comp continuous_star) F.continuous.star) x
    rintro _ ⟨a, rfl⟩
    change F (star (i a)) = star (F (i a))
    rw [← map_star i, heq, heq, map_star f]
  have hmul (x y : S.topologicalClosure) : F (x * y) = F x * F y := by
    have hcont : Continuous F := F.continuous
    refine hd.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
    rintro _ ⟨a, rfl⟩
    refine hd.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) y
    rintro _ ⟨b, rfl⟩
    change F (i a * i b) = F (i a) * F (i b)
    rw [← map_mul i, heq, heq, heq, map_mul f]
  let g : S.topologicalClosure →⋆ₙₐ[ℂ] B :=
    { toFun := F
      map_zero' := F.map_zero
      map_add' := F.map_add
      map_smul' := F.map_smul
      map_mul' := hmul
      map_star' := hstar }
  exact ⟨g, heq, hF_norm⟩

end MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.CAR

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Compatible surjective finite-stage quotients give a genuine surjection
from the norm closure of the actual increasing union to the existing CAR
completion. The theorem constructs the hom; no final quotient or completion
map is included among its assumptions. -/
theorem exists_surjective_hom_topologicalClosure_iSup
    (D : ℕ → NonUnitalStarSubalgebra ℂ A) (hD : Monotone D)
    (hclosed : ∀ n, IsClosed (D n : Set A))
    (q : ∀ n, D n →⋆ₙₐ[ℂ] Stage n)
    (hq : ∀ n, Function.Surjective (q n))
    (hcomp : ∀ (n m : ℕ) (h : n ≤ m) (x : D n),
      q m (NonUnitalStarSubalgebra.inclusion (hD h) x) = embed n m h (q n x)) :
    ∃ Q : (⨆ n, D n).topologicalClosure →⋆ₙₐ[ℂ] Limit,
      Function.Surjective Q ∧
      ∀ (n : ℕ) (x : D n),
        Q (NonUnitalStarSubalgebra.inclusion
          ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure _)) x) =
          ofStage n (q n x) := by
  let F (n : ℕ) : D n →⋆ₙₐ[ℂ] Limit :=
    (ofStage n).toNonUnitalStarAlgHom.comp (q n)
  have hF (n m : ℕ) (h : n ≤ m) (x : D n) :
      F m (NonUnitalStarSubalgebra.inclusion (hD h) x) = F n x := by
    change ofStage m (q m (NonUnitalStarSubalgebra.inclusion (hD h) x)) =
      ofStage n (q n x)
    rw [hcomp n m h x, ofStage_embed n m h (q n x)]
  have hF_overlap (n m : ℕ) (h : D n ≤ D m) :
      F n = (F m).comp (NonUnitalStarSubalgebra.inclusion h) := by
    ext x
    let k := max n m
    have hn : n ≤ k := le_max_left _ _
    have hm : m ≤ k := le_max_right _ _
    calc
      F n x = F k (NonUnitalStarSubalgebra.inclusion (hD hn) x) := (hF n k hn x).symm
      _ = F k (NonUnitalStarSubalgebra.inclusion (hD hm)
            (NonUnitalStarSubalgebra.inclusion h x)) := by
        apply congrArg (F k)
        exact Subtype.ext rfl
      _ = F m (NonUnitalStarSubalgebra.inclusion h x) := hF m k hm _
  let U : NonUnitalStarSubalgebra ℂ A := ⨆ n, D n
  let f : U →⋆ₙₐ[ℂ] Limit :=
    NonUnitalStarSubalgebra.iSupLift D hD.directed_le F hF_overlap U rfl
  have hf (x : U) : ‖f x‖ ≤ ‖x‖ := by
    have hx : (x : A) ∈ ⋃ n, (D n : Set A) := by
      rw [← NonUnitalStarSubalgebra.coe_iSup_of_directed hD.directed_le]
      exact x.property
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    letI : IsClosed (D n : Set A) := hclosed n
    change ‖NonUnitalStarSubalgebra.iSupLift D hD.directed_le F hF_overlap U rfl x‖ ≤ ‖x‖
    rw [NonUnitalStarSubalgebra.iSupLift_of_mem x hxn]
    exact NonUnitalStarAlgHom.norm_apply_le (F n) ⟨x, hxn⟩
  obtain ⟨Q, hQ, _hQnorm⟩ :=
    MathlibAnnex.Analysis.CStarAlgebra.exists_starAlgHom_extension_topologicalClosure U f hf
  have hstage (n : ℕ) (x : D n) :
      Q (NonUnitalStarSubalgebra.inclusion
        ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure U)) x) =
        ofStage n (q n x) := by
    change Q (NonUnitalStarSubalgebra.inclusion U.le_topologicalClosure
      (NonUnitalStarSubalgebra.inclusion (le_iSup D n) x)) = _
    rw [hQ]
    change NonUnitalStarSubalgebra.iSupLift D hD.directed_le F hF_overlap U rfl
      (NonUnitalStarSubalgebra.inclusion (le_iSup D n) x) = _
    rw [NonUnitalStarSubalgebra.iSupLift_inclusion]
    rfl
  have hrange : (⋃ n, Set.range (ofStage n)) ⊆ Set.range Q := by
    intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨x, hx⟩ := hq n a
    refine ⟨NonUnitalStarSubalgebra.inclusion
      ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure U)) x, ?_⟩
    rw [hstage, hx]
  have hdense : Dense (Set.range Q) := dense_stageRange.mono hrange
  letI : IsClosed (U.topologicalClosure : Set A) :=
    NonUnitalStarSubalgebra.isClosed_topologicalClosure U
  letI : PartialOrder U.topologicalClosure :=
    _root_.CStarAlgebra.spectralOrder U.topologicalClosure
  letI : StarOrderedRing U.topologicalClosure :=
    _root_.CStarAlgebra.spectralOrderedRing U.topologicalClosure
  have hQclosed : IsClosed (Set.range Q) :=
    MathlibAnnex.Analysis.CStarAlgebra.HomKernelQuotient.isClosed_range Q
  refine ⟨Q, ?_, hstage⟩
  intro y
  have hy : y ∈ closure (Set.range Q) := hdense y
  rwa [hQclosed.closure_eq] at hy

/-- Adjacent compatibility suffices: the finite quotient maps are transported
along the actual iterated `CAR.embed`, proved by induction on the stage gap. -/
theorem exists_surjective_hom_topologicalClosure_iSup_of_step
    (D : ℕ → NonUnitalStarSubalgebra ℂ A) (hD : Monotone D)
    (hclosed : ∀ n, IsClosed (D n : Set A))
    (q : ∀ n, D n →⋆ₙₐ[ℂ] Stage n)
    (hq : ∀ n, Function.Surjective (q n))
    (hstep : ∀ (n : ℕ) (x : D n),
      q (n + 1) (NonUnitalStarSubalgebra.inclusion (hD (Nat.le_succ n)) x) =
        step n (q n x)) :
    ∃ Q : (⨆ n, D n).topologicalClosure →⋆ₙₐ[ℂ] Limit,
      Function.Surjective Q ∧
      ∀ (n : ℕ) (x : D n),
        Q (NonUnitalStarSubalgebra.inclusion
          ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure _)) x) =
          ofStage n (q n x) := by
  have hcomp (n : ℕ) : ∀ (m : ℕ) (h : n ≤ m) (x : D n),
      q m (NonUnitalStarSubalgebra.inclusion (hD h) x) = embed n m h (q n x) := by
    apply Nat.le_induction
    · intro x
      rw [embed_refl n]
      rfl
    · intro m h ih x
      calc
        q (m + 1) (NonUnitalStarSubalgebra.inclusion (hD (Nat.le.step h)) x) =
            q (m + 1) (NonUnitalStarSubalgebra.inclusion (hD (Nat.le_succ m))
              (NonUnitalStarSubalgebra.inclusion (hD h) x)) := rfl
        _ = step m (q m (NonUnitalStarSubalgebra.inclusion (hD h) x)) := hstep m _
        _ = step m (embed n m h (q n x)) := congrArg (step m) (ih x)
        _ = embed n (m + 1) (Nat.le.step h) (q n x) := by
          rw [embed_succ n m h]
          rfl
  exact exists_surjective_hom_topologicalClosure_iSup D hD hclosed q hq hcomp

end MathlibAnnex.CStarAlgebra.CAR
