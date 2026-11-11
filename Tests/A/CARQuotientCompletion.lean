/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CARQuotientCompletion

set_option autoImplicit false
noncomputable section
open Set
open scoped CStarAlgebra

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B]

-- S may be incomplete. Only the range algebra B is assumed complete.
example (S : NonUnitalStarSubalgebra ℂ A) (f : S →⋆ₙₐ[ℂ] B)
    (hf : ∀ x : S, ‖f x‖ ≤ ‖x‖) :
    ∃ g : S.topologicalClosure →⋆ₙₐ[ℂ] B,
      (∀ x : S, g (NonUnitalStarSubalgebra.inclusion S.le_topologicalClosure x) = f x) ∧
      (∀ x : S.topologicalClosure, ‖g x‖ ≤ ‖x‖) :=
  MathlibAnnex.Analysis.CStarAlgebra.exists_starAlgHom_extension_topologicalClosure
    (S := S) (f := f) hf

open MathlibAnnex.CStarAlgebra.CAR

example (D : ℕ → NonUnitalStarSubalgebra ℂ A) (hD : Monotone D)
    (hclosed : ∀ n, IsClosed (D n : Set A))
    (q : ∀ n, D n →⋆ₙₐ[ℂ] Stage n)
    (hq : ∀ n, Function.Surjective (q n))
    (hcomp : ∀ n m (h : n ≤ m) (x : D n),
      q m (NonUnitalStarSubalgebra.inclusion (hD h) x) = embed n m h (q n x)) :
    ∃ Q : (⨆ n, D n).topologicalClosure →⋆ₙₐ[ℂ] Limit,
      Function.Surjective Q ∧
      ∀ n (x : D n), Q (NonUnitalStarSubalgebra.inclusion
        ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure _)) x) =
        ofStage n (q n x) :=
  exists_surjective_hom_topologicalClosure_iSup (D := D) hD hclosed q hq hcomp

-- Only adjacent compatibility is supplied; arbitrary-gap compatibility is proved.
example (D : ℕ → NonUnitalStarSubalgebra ℂ A) (hD : Monotone D)
    (hclosed : ∀ n, IsClosed (D n : Set A))
    (q : ∀ n, D n →⋆ₙₐ[ℂ] Stage n)
    (hq : ∀ n, Function.Surjective (q n))
    (hstep : ∀ n (x : D n),
      q (n + 1) (NonUnitalStarSubalgebra.inclusion (hD (Nat.le_succ n)) x) =
        step n (q n x)) :
    ∃ Q : (⨆ n, D n).topologicalClosure →⋆ₙₐ[ℂ] Limit,
      Function.Surjective Q ∧
      ∀ n (x : D n), Q (NonUnitalStarSubalgebra.inclusion
        ((le_iSup D n).trans (NonUnitalStarSubalgebra.le_topologicalClosure _)) x) =
        ofStage n (q n x) :=
  exists_surjective_hom_topologicalClosure_iSup_of_step (D := D) hD hclosed q hq hstep

