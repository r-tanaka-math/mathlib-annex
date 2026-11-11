/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryStageAction

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MathlibAnnex.CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

example (n : ℕ) (M : CAR.Stage n) (i j : Fin (2 ^ n)) (s t : Fin 2) :
    CAR.step n M (CAR.stepIndexEquiv n (i, s)) (CAR.stepIndexEquiv n (j, t)) =
      if s = t then M i j else 0 :=
  CAR.step_apply_stepIndexEquiv n M i j s t

example (n : ℕ) (M : CAR.Stage n) (i : Fin (2 ^ n)) (s : Fin 2)
    (f : Fin (2 ^ (n + 1)) → A) :
    (∑ k, CAR.step n M k (CAR.stepIndexEquiv n (i, s)) • f k) =
      ∑ k, M k i • f (CAR.stepIndexEquiv n (k, s)) :=
  CAR.sum_step_column_smul n M i s f

example (n : ℕ) (M : CAR.Stage n) (j : Fin (2 ^ n)) (t : Fin 2)
    (f : Fin (2 ^ (n + 1)) → A) :
    (∑ k, CAR.step n M (CAR.stepIndexEquiv n (j, t)) k • f k) =
      ∑ k, M j k • f (CAR.stepIndexEquiv n (k, t)) :=
  CAR.sum_step_row_smul n M j t f

example (b v : ℕ → A) (n : ℕ) (i j : Fin (2 ^ n))
    (z : hereditarySubalgebra (b n)) :
    star (hereditaryStageCoreEntry b v n i j z) =
      hereditaryStageCoreEntry b v n j i (star z) :=
  star_hereditaryStageCoreEntry b v n i j z

example (b v : ℕ → A) (n : ℕ)
    (hcore : hereditarySubalgebra (b (n + 1)) ≤ hereditarySubalgebra (b n))
    (hv : v n ∈ hereditarySubalgebra (b n)) {a : A} {M : CAR.Stage n}
    (hM : ActsOnMatrixCorners (hereditaryStageCoreEntry b v n) a M) :
    ActsOnMatrixCorners (hereditaryStageCoreEntry b v (n + 1)) a (CAR.step n M) :=
  hM.hereditaryStageCoreEntry_step b v n hcore hv
