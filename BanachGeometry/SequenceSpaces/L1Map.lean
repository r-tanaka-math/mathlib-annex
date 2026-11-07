import BanachGeometry.AlmostIsometric.PointedBiLip

/-!
# Pointed coordinate maps on heterogeneous ℓ₁ sums

R6 §3, equations (3.7)--(3.10): summability is proved from the
pointed norm estimate, and the same constant is retained in both directions.
No additivity of the coordinate maps is needed.
-/

noncomputable section
open scoped ENNReal
namespace BanachGeometry

universe u v w
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]

abbrev L1Sum (E : ι → Type v) [∀ i, NormedAddCommGroup (E i)] := lp E 1

theorem l1_summable (x : L1Sum E) : Summable (fun i => ‖x i‖) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem l1_norm_eq_tsum (x : L1Sum E) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) x

/-- Membership lemma used for the forward and inverse branch maps. -/
theorem l1_coordinate_summable (C : ℝ) (e : ∀ i, PointedBiLip (E i) (F i) C)
    (x : L1Sum E) : Summable (fun i => ‖(e i).equiv (x i)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => (e i).norm_le _) ((l1_summable x).mul_left C)

def l1Map (C : ℝ) (e : ∀ i, PointedBiLip (E i) (F i) C)
    (x : L1Sum E) : L1Sum F :=
  ⟨fun i => (e i).equiv (x i), by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).2
    simpa using l1_coordinate_summable C e x⟩

@[simp] theorem l1Map_apply (C : ℝ) (e : ∀ i, PointedBiLip (E i) (F i) C)
    (x : L1Sum E) (i : ι) : l1Map C e x i = (e i).equiv (x i) := rfl

/-- Explicit norm estimate on differences, using the actual ℓ₁ norm. -/
theorem l1Map_difference_le (C : ℝ) (e : ∀ i, PointedBiLip (E i) (F i) C)
    (x y : L1Sum E) : ‖l1Map C e x - l1Map C e y‖ ≤ C * ‖x - y‖ := by
  rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
  calc
    (∑' i, ‖(l1Map C e x - l1Map C e y) i‖) ≤
        ∑' i, C * ‖(x - y) i‖ := by
      apply Summable.tsum_le_tsum
      · intro i; exact (e i).forward _ _
      · exact l1_summable _
      · exact (l1_summable (x - y)).mul_left C
    _ = C * ∑' i, ‖(x - y) i‖ := by rw [tsum_mul_left]

/-- Coordinatewise lifting of a uniformly bounded pointed equivalence to ℓ₁. -/
def l1BiLip (C : ℝ) (e : ∀ i, PointedBiLip (E i) (F i) C) :
    PointedBiLip (L1Sum E) (L1Sum F) C where
  equiv := {
    toFun := l1Map C e
    invFun := l1Map C (fun i => (e i).symm)
    left_inv := by intro x; apply lp.ext; funext i; exact (e i).equiv.symm_apply_apply _
    right_inv := by intro y; apply lp.ext; funext i; exact (e i).equiv.apply_symm_apply _ }
  zero_eq := by apply lp.ext; funext i; exact (e i).zero_eq
  forward := l1Map_difference_le C e
  backward := l1Map_difference_le C (fun i => (e i).symm)

end BanachGeometry
