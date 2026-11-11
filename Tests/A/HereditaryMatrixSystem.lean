/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.HereditaryMatrixSystem

noncomputable section
set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra MathlibAnnex.CStarAlgebra
open scoped CStarAlgebra

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

example (v : ℕ → A) (n : ℕ) (i j : Fin (2 ^ n)) (b d : Fin 2) (z : A) :
    hereditaryStageEntry v (n + 1) (CAR.stepIndexEquiv n (i, b))
      (CAR.stepIndexEquiv n (j, d)) z =
      hereditaryStageEntry v n i j
        (hereditaryMatrixEntry (v n) (decide (b ≠ 0)) (decide (d ≠ 0)) z) :=
  hereditaryStageEntry_step v n i j b d z

example (v : ℕ → A) (n : ℕ) (i j : Fin (2 ^ n)) (z : A) :
    star (hereditaryStageEntry v n i j z) = hereditaryStageEntry v n j i (star z) :=
  star_hereditaryStageEntry v n i j z

example {a : A} (v : ℕ → A) (n : ℕ)
    (hv : ∀ k < n, v k ∈ hereditarySubalgebra a)
    (i j : Fin (2 ^ n)) {z : A} (hz : z ∈ hereditarySubalgebra a) :
    hereditaryStageEntry v n i j z ∈ hereditarySubalgebra a :=
  hereditaryStageEntry_mem v n hv i j hz

example (c v : ℕ → A) (hc : ∀ n, IsSelfAdjoint (c n))
    (hchild : ∀ n, c (n + 1) ∈ hereditarySubalgebra (c n))
    (hlink : ∀ n, v n ∈ hereditarySubalgebra (c n))
    (hfix : ∀ n, star (v n) * v n * c (n + 1) = c (n + 1))
    (n : ℕ) (i j : Fin (2 ^ n)) {z : A} (hz : z ∈ hereditarySubalgebra (c n)) :
    ‖hereditaryStageEntry v n i j z‖ = ‖z‖ :=
  norm_hereditaryStageEntry c v hc hchild hlink hfix n i j hz

example (c v : ℕ → A) (hc : ∀ n, IsSelfAdjoint (c n))
    (hchild : ∀ n, c (n + 1) ∈ hereditarySubalgebra (c n))
    (hlink : ∀ n, v n ∈ hereditarySubalgebra (c n))
    (hfix : ∀ n, star (v n) * v n * c (n + 1) = c (n + 1))
    (hzero : ∀ n, c (n + 1) * v n = 0)
    (n : ℕ) (i j k l : Fin (2 ^ n)) {z w : A}
    (hz : z ∈ hereditarySubalgebra (c n)) (hw : w ∈ hereditarySubalgebra (c n)) :
    hereditaryStageEntry v n i j z * hereditaryStageEntry v n k l w =
      if j = k then hereditaryStageEntry v n i l (z * w) else 0 :=
  hereditaryStageEntry_mul c v hc hchild hlink hfix hzero n i j k l hz hw

-- The recursive witness keeps its nonzero coefficients and exact fixing equations.
example (hA : IsAntiliminal A) {a : A} (ha : 0 ≤ a) (ha0 : a ≠ 0) :
    ∃ c v : ℕ → A, c 0 = a ∧ (∀ n, 0 ≤ c n ∧ c n ≠ 0) ∧
      (∀ n, star (v n) * v n * c (n + 1) = c (n + 1) ∧ c (n + 1) * v n = 0) := by
  obtain ⟨c, b, e, v, h0, hc, _hb, hv⟩ := hA.exists_hereditary_matrix_data ha ha0
  refine ⟨c, v, h0, hc, ?_⟩
  intro n
  exact ⟨(hv n).2.2.2.2.1, (hv n).2.2.2.2.2⟩
