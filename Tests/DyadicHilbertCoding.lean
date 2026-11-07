/- W02 fresh consumer. Prepared only; no Lean execution in this stage. -/
import BanachGeometry.AlmostIsometric.Existence
import BanachGeometry.AlmostIsometric.Consequences
import BanachGeometry.LipschitzFreeSpace.PositiveTailLocality
open BanachGeometry BanachGeometry.HilbertSums BanachGeometry.HilbertSums.Coding
open scoped BigOperators InnerProductSpace
noncomputable section

example : Fintype.card (GridPoint 1) = 3 := by norm_num [card_gridPoint]
example : Fintype.card (GridPoint 2) = 25 := by norm_num [card_gridPoint]
example : Fintype.card (GridPoint 3) = 343 := by norm_num [card_gridPoint]
example (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    1 / 2 ≤ ‖tentVector k x‖ := one_half_le_norm_tentVector k x hx
example (k : ℕ) (x : Fin k → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ‖unitCode k x‖ = 1 := norm_unitCode k x hx
example (x : Fin 0 → ℝ) : ‖unitCode 0 x‖ = 1 :=
  norm_unitCode 0 x (fun j => Fin.elim0 j)
example {k : ℕ} (hk : 0 < k) (x z : Fin k → ℝ)
    (hx : ∀ j, |x j| ≤ 1) (hz : ∀ j, |z j| ≤ 1)
    (j : Fin k) (hj : 2 / (k : ℝ) ≤ |x j - z j|) :
    Disjoint (Function.support (unitCode k x)) (Function.support (unitCode k z)) :=
  unitCode_support_disjoint hk x z hx hz j hj

example (c : ℝ) (m : ℕ) :
    clockOnBand c m (dyadicRadius (m + 1)) = clockOnBand c (m + 1) (dyadicRadius (m + 1)) := by
  rw [clockOnBand_lower_endpoint, clockOnBand_upper_endpoint]
example (c : ℝ) : (∑' m, dyadicRadius m ^ 2 * dyadicSlope c m ^ 2) ≤ c ^ 2 / 32 :=
  dyadic_weight_total_le c
example (m : ℕ) : dyadicSlope (1 / 8) m * (dyadicRadius m - dyadicRadius (m + 1)) =
    (1 / 8 : ℝ) / (16 * (m + 1)) := dyadic_band_increment _ _

section HilbertBlocks
variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℝ (G n)]
example (y : lp G 2) (N : ℕ) :
    ‖blockTail N y‖ ^ 2 - ‖blockTail (N + 1) y‖ ^ 2 = ‖y N‖ ^ 2 := norm_blockTail_sq_sub_norm_blockTail_succ_sq N y
example (k N : ℕ) (b : Fin k → ℕ) (e : ∀ j, G (b j)) (hb : ∀ j, b j < N) (y : lp G 2) :
    observedUnitCode k b e (blockHead N y) = observedUnitCode k b e y :=
  observedUnitCode_head k N b e hb y
end HilbertBlocks
