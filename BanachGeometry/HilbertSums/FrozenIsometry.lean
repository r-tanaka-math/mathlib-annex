/-
Fixed Pair R6 Lemma 9.2: ℓ₂ membership, total energy, and an actual isometric
equivalence for the frozen unit directions. These constructions feed the
inverse-map comparison estimates. Local execution status is recorded in the
external qualification receipts.
-/
import BanachGeometry.HilbertSums.FrozenRearrangement
import BanachGeometry.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped ENNReal

noncomputable section
open scoped InnerProductSpace BigOperators
namespace BanachGeometry.HilbertSums

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℝ (G n)]

theorem l2_summable_sq (u : lp G 2) : Summable (fun n => ‖u n‖ ^ 2) := by
  simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

theorem l2_norm_sq (u : lp G 2) : ‖u‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u

theorem mem_l2_of_summable_sq (u : ∀ n, G n) (h : Summable (fun n => ‖u n‖ ^ 2)) :
    Memℓp u 2 := by
  apply memℓp_gen
  simpa using h

theorem summable_interleave_sq (a v : ℕ → ℝ)
    (ha : Summable (fun n => a n ^ 2)) (hv : Summable (fun n => v n ^ 2)) :
    Summable (fun n => interleave a v n ^ 2) := by
  apply Summable.even_add_odd
  · simpa only [interleave_even] using hv
  · simpa only [interleave_odd] using ha

theorem tsum_interleave_sq (a v : ℕ → ℝ)
    (ha : Summable (fun n => a n ^ 2)) (hv : Summable (fun n => v n ^ 2)) :
    (∑' n, interleave a v n ^ 2) = (∑' n, a n ^ 2) + ∑' n, v n ^ 2 := by
  have he : Summable (fun n => interleave a v (2 * n) ^ 2) := by
    simpa only [interleave_even] using hv
  have ho : Summable (fun n => interleave a v (2 * n + 1) ^ 2) := by
    simpa only [interleave_odd] using ha
  have ht := tsum_even_add_odd (f := fun n => interleave a v n ^ 2) he ho
  calc
    _ = (∑' n, v n ^ 2) + ∑' n, a n ^ 2 := by
      simpa only [interleave_even, interleave_odd] using ht.symm
    _ = _ := add_comm _ _

variable (ξ : ∀ n, G n) (hξ : ∀ n, ‖ξ n‖ = 1)
include hξ

theorem coefficient_sq_summable (u : lp G 2) :
    Summable (fun n => coefficient ξ (fun k => u k) n ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (l2_summable_sq u)
  intro n
  have h := coefficient_abs_le ξ hξ (fun k => u k) n
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 h

theorem frozenForward_sq_summable (u : lp G 2) (v : ScalarL2) :
    Summable (fun n => ‖frozenForward ξ (fun k => u k) (fun k => v k) n‖ ^ 2) := by
  have ha := coefficient_sq_summable ξ hξ u
  have hv : Summable (fun n => v n ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using l2_summable_sq v
  have hc := summable_interleave_sq (coefficient ξ (fun k => u k)) (fun k => v k) ha hv
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((l2_summable_sq u).add hc)
  intro n
  rw [frozenForward_energy ξ hξ]
  linarith [sq_nonneg (coefficient ξ (fun k => u k) n)]

theorem frozenInverseU_sq_summable (y : lp G 2) :
    Summable (fun n => ‖frozenInverseU ξ (fun k => y k) n‖ ^ 2) := by
  have ha := coefficient_sq_summable ξ hξ y
  have ho : Summable (fun n => coefficient ξ (fun k => y k) (2 * n + 1) ^ 2) :=
    ha.comp_injective (by
      intro i j h
      change 2 * i + 1 = 2 * j + 1 at h
      omega)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((l2_summable_sq y).add ho)
  intro n
  rw [frozenInverseU_energy ξ hξ]
  linarith [sq_nonneg (coefficient ξ (fun k => y k) n)]

theorem frozenInverseV_sq_summable (y : lp G 2) :
    Summable (fun n => frozenInverseV ξ (fun k => y k) n ^ 2) :=
  (coefficient_sq_summable ξ hξ y).comp_injective (by intro i j h; omega)

def frozenForwardL2 (u : lp G 2) (v : ScalarL2) : lp G 2 :=
  ⟨frozenForward ξ (fun k => u k) (fun k => v k),
    mem_l2_of_summable_sq _ (frozenForward_sq_summable ξ hξ u v)⟩

def frozenInverseUL2 (y : lp G 2) : lp G 2 :=
  ⟨frozenInverseU ξ (fun k => y k),
    mem_l2_of_summable_sq _ (frozenInverseU_sq_summable ξ hξ y)⟩

def frozenInverseVL2 (y : lp G 2) : ScalarL2 :=
  ⟨frozenInverseV ξ (fun k => y k), mem_l2_of_summable_sq _ (by
    simpa only [Real.norm_eq_abs, sq_abs] using frozenInverseV_sq_summable ξ hξ y)⟩

@[simp] theorem frozenForwardL2_apply (u : lp G 2) (v : ScalarL2) (n : ℕ) :
    frozenForwardL2 ξ hξ u v n = frozenForward ξ (fun k => u k) (fun k => v k) n := rfl

@[simp] theorem frozenInverseUL2_apply (y : lp G 2) (n : ℕ) :
    frozenInverseUL2 ξ hξ y n = frozenInverseU ξ (fun k => y k) n := rfl

@[simp] theorem frozenInverseVL2_apply (y : lp G 2) (n : ℕ) :
    frozenInverseVL2 ξ hξ y n = frozenInverseV ξ (fun k => y k) n := rfl

/-- The actual equivalence on the contract's L² product, with both compositions proved. -/
def frozenL2Equiv : HilbertPair (lp G 2) ≃ lp G 2 where
  toFun z := frozenForwardL2 ξ hξ (WithLp.ofLp z).1 (WithLp.ofLp z).2
  invFun y := WithLp.toLp 2 (frozenInverseUL2 ξ hξ y, frozenInverseVL2 ξ hξ y)
  left_inv z := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply lp.ext
      funext n
      exact congrFun (frozenInverseU_forward ξ hξ
        (fun k => (WithLp.ofLp z).1 k) (fun k => (WithLp.ofLp z).2 k)) n
    · apply lp.ext
      funext n
      exact congrFun (frozenInverseV_forward ξ hξ
        (fun k => (WithLp.ofLp z).1 k) (fun k => (WithLp.ofLp z).2 k)) n
  right_inv y := by
    apply lp.ext
    funext n
    exact congrFun (frozenForward_inverse ξ hξ (fun k => y k)) n

theorem frozenForward_total_energy (u : lp G 2) (v : ScalarL2) :
    ‖frozenForwardL2 ξ hξ u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have hu := l2_summable_sq u
  have ha := coefficient_sq_summable ξ hξ u
  have hv : Summable (fun n => v n ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using l2_summable_sq v
  have hc := summable_interleave_sq (coefficient ξ (fun k => u k)) (fun k => v k) ha hv
  rw [l2_norm_sq, l2_norm_sq u, l2_norm_sq v]
  simp only [frozenForwardL2_apply, frozenForward_energy ξ hξ, Real.norm_eq_abs, sq_abs]
  rw [(hu.sub ha).tsum_add hc, hu.tsum_sub ha, tsum_interleave_sq _ _ ha hv]
  ring

theorem norm_frozenL2Equiv (z : HilbertPair (lp G 2)) :
    ‖frozenL2Equiv ξ hξ z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  exact (frozenForward_total_energy ξ hξ (WithLp.ofLp z).1 (WithLp.ofLp z).2).trans
    (WithLp.prod_norm_sq_eq_of_L2 z).symm

omit hξ in
/-- Additivity of the raw interleaving, needed for the linear isometry export. -/
theorem interleave_add (a b v w : ℕ → ℝ) (n : ℕ) :
    interleave (a + b) (v + w) n = interleave a v n + interleave b w n := by
  unfold interleave
  split_ifs <;> rfl

omit hξ in
theorem interleave_smul (c : ℝ) (a v : ℕ → ℝ) (n : ℕ) :
    interleave (c • a) (c • v) n = c * interleave a v n := by
  unfold interleave
  split_ifs <;> rfl

omit hξ in
private theorem frozenForward_add (u u' : ∀ n, G n) (v v' : ℕ → ℝ) (n : ℕ) :
    frozenForward ξ (u + u') (v + v') n =
      frozenForward ξ u v n + frozenForward ξ u' v' n := by
  have hc : coefficient ξ (u + u') = coefficient ξ u + coefficient ξ u' := by
    funext k
    exact inner_add_right _ _ _
  dsimp only [frozenForward]
  rw [hc, interleave_add]
  simp only [Pi.add_apply]
  module

omit hξ in
private theorem frozenForward_smul (c : ℝ) (u : ∀ n, G n) (v : ℕ → ℝ) (n : ℕ) :
    frozenForward ξ (c • u) (c • v) n = c • frozenForward ξ u v n := by
  have hc : coefficient ξ (c • u) = c • coefficient ξ u := by
    funext k
    exact real_inner_smul_right _ _ _
  dsimp only [frozenForward]
  rw [hc, interleave_smul]
  simp only [Pi.smul_apply]
  module

/-- R6 Lemma 9.2, with arbitrary real inner product blocks (in particular finite dimensional). -/
def frozenLinearIsometryEquiv : HilbertPair (lp G 2) ≃ₗᵢ[ℝ] lp G 2 where
  toFun := frozenL2Equiv ξ hξ
  invFun := (frozenL2Equiv ξ hξ).symm
  left_inv := (frozenL2Equiv ξ hξ).left_inv
  right_inv := (frozenL2Equiv ξ hξ).right_inv
  map_add' z w := by
    apply lp.ext
    funext n
    change frozenForward ξ (fun k => (WithLp.ofLp (z + w)).1 k)
      (fun k => (WithLp.ofLp (z + w)).2 k) n =
      frozenForward ξ (fun k => (WithLp.ofLp z).1 k) (fun k => (WithLp.ofLp z).2 k) n +
      frozenForward ξ (fun k => (WithLp.ofLp w).1 k) (fun k => (WithLp.ofLp w).2 k) n
    exact frozenForward_add ξ (fun k => (WithLp.ofLp z).1 k)
      (fun k => (WithLp.ofLp w).1 k) (fun k => (WithLp.ofLp z).2 k)
      (fun k => (WithLp.ofLp w).2 k) n
  map_smul' c z := by
    apply lp.ext
    funext n
    change frozenForward ξ (fun k => (WithLp.ofLp (c • z)).1 k)
      (fun k => (WithLp.ofLp (c • z)).2 k) n =
      c • frozenForward ξ (fun k => (WithLp.ofLp z).1 k) (fun k => (WithLp.ofLp z).2 k) n
    exact frozenForward_smul ξ c (fun k => (WithLp.ofLp z).1 k)
      (fun k => (WithLp.ofLp z).2 k) n
  norm_map' := norm_frozenL2Equiv ξ hξ

end BanachGeometry.HilbertSums
