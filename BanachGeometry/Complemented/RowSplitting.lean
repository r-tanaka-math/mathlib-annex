import BanachGeometry.AlmostIsometric.CriterionAssembly
import BanachGeometry.WeakSequences.CountableExclusion
import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-! R6 (one-summand-split): each mixed row is linearly isomorphic to one
Y-only ℓ₁ row and k copies of C0L2. Only the first k H3 maps are bounded
by the displayed finite constant. No uniform H3 assumption is added.
Local execution status is recorded in the external qualification receipts. -/
noncomputable section
namespace BanachGeometry
namespace RowSplitting
variable (d : AlmostIsometricFamily) (e : ∀ i, (d.X i).Carrier ≃L[ℝ] ((d.Y i).Carrier × C0L2))
    (k : ℕ)
abbrev G := L1Sum (fun i => (d.Y i).Carrier)
abbrev D := Fin k → C0L2

def headEquiv (r : Fin k) : (d.mixed k r.val).Carrier ≃L[ℝ] ((d.Y r.val).Carrier × C0L2) := by
  exact Eq.mpr (congrArg (fun Z : SeparableRealBanach =>
    Z.Carrier ≃L[ℝ] ((d.Y r.val).Carrier × C0L2)) (d.mixed_head k r.val r.isLt)) (e r.val)

def tailIsometry (i : ℕ) (hi : ¬ i < k) : (d.mixed k i).Carrier ≃ₗᵢ[ℝ] (d.Y i).Carrier := by
  exact Eq.mpr (congrArg (fun Z : SeparableRealBanach =>
    Z.Carrier ≃ₗᵢ[ℝ] (d.Y i).Carrier) (d.mixed_tail k i (Nat.le_of_not_gt hi)))
    (LinearIsometryEquiv.refl ℝ (d.Y i).Carrier)

def tailEquiv (i : ℕ) (hi : ¬ i < k) : (d.mixed k i).Carrier ≃L[ℝ] (d.Y i).Carrier :=
  (tailIsometry d k i hi).toContinuousLinearEquiv

def toYCoord (i : ℕ) : (d.mixed k i).Carrier →L[ℝ] (d.Y i).Carrier :=
  if hi : i < k then
    (ContinuousLinearMap.fst ℝ (d.Y i).Carrier C0L2).comp (headEquiv d e k ⟨i,hi⟩).toContinuousLinearMap
  else (tailEquiv d k i hi).toContinuousLinearMap

def fromYCoord (i : ℕ) : (d.Y i).Carrier →L[ℝ] (d.mixed k i).Carrier :=
  if hi : i < k then
    (headEquiv d e k ⟨i,hi⟩).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (d.Y i).Carrier C0L2)
  else (tailEquiv d k i hi).symm.toContinuousLinearMap

def toHCoord (r : Fin k) : (d.mixed k r.val).Carrier →L[ℝ] C0L2 :=
  (ContinuousLinearMap.snd ℝ (d.Y r.val).Carrier C0L2).comp (headEquiv d e k r).toContinuousLinearMap

def fromHCoord (r : Fin k) : C0L2 →L[ℝ] (d.mixed k r.val).Carrier :=
  (headEquiv d e k r).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (d.Y r.val).Carrier C0L2)

theorem toYCoord_fromYCoord (i : ℕ) (y : (d.Y i).Carrier) : toYCoord d e k i (fromYCoord d e k i y) = y := by
  by_cases hi : i < k
  · simp only [toYCoord, fromYCoord, dif_pos hi, ContinuousLinearMap.comp_apply]
    change ((headEquiv d e k ⟨i,hi⟩) ((headEquiv d e k ⟨i,hi⟩).symm (y,0))).1 = y
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · simp only [toYCoord, fromYCoord, dif_neg hi]
    exact (tailEquiv d k i hi).apply_symm_apply y

theorem toHCoord_fromYCoord (r : Fin k) (y : (d.Y r.val).Carrier) :
    toHCoord d e k r (fromYCoord d e k r.val y) = 0 := by
  simp only [fromYCoord, dif_pos r.isLt, toHCoord, ContinuousLinearMap.comp_apply]
  change ((headEquiv d e k r) ((headEquiv d e k r).symm (y,0))).2 = 0
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem toYCoord_fromHCoord (r : Fin k) (v : C0L2) : toYCoord d e k r.val (fromHCoord d e k r v) = 0 := by
  simp only [toYCoord, dif_pos r.isLt, fromHCoord, ContinuousLinearMap.comp_apply]
  change ((headEquiv d e k r) ((headEquiv d e k r).symm (0,v))).1 = 0
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem toHCoord_fromHCoord (r : Fin k) (v : C0L2) : toHCoord d e k r (fromHCoord d e k r v) = v := by
  change ((headEquiv d e k r) ((headEquiv d e k r).symm (0,v))).2 = v
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem recover_head (r : Fin k) (x : (d.mixed k r.val).Carrier) :
    fromYCoord d e k r.val (toYCoord d e k r.val x) +
      fromHCoord d e k r (toHCoord d e k r x) = x := by
  simp only [fromYCoord, toYCoord, dif_pos r.isLt, fromHCoord, toHCoord,
    ContinuousLinearMap.comp_apply]
  change (headEquiv d e k r).symm (((headEquiv d e k r) x).1,0) +
    (headEquiv d e k r).symm (0,((headEquiv d e k r) x).2) = x
  rw [← map_add]
  have hz : (((headEquiv d e k r) x).1, (0 : C0L2)) +
      (0, ((headEquiv d e k r) x).2) = (headEquiv d e k r) x := by
    apply Prod.ext <;> simp
  rw [hz]
  exact (headEquiv d e k r).symm_apply_apply x

theorem recover_tail (i : ℕ) (hi : ¬ i < k) (x : (d.mixed k i).Carrier) :
    fromYCoord d e k i (toYCoord d e k i x) = x := by
  simp only [toYCoord, fromYCoord, dif_neg hi]
  exact (tailEquiv d k i hi).symm_apply_apply x

def bound : ℝ := 1 + ∑ r : Fin k, (‖toYCoord d e k r.val‖ + ‖fromYCoord d e k r.val‖)

theorem norm_toYCoord_le_bound (i : ℕ) : ‖toYCoord d e k i‖ ≤ bound d e k := by
  have hs : 0 ≤ ∑ r : Fin k, (‖toYCoord d e k r.val‖ + ‖fromYCoord d e k r.val‖) :=
    Finset.sum_nonneg (fun r hr => by positivity)
  by_cases hi : i < k
  · have hf := Finset.single_le_sum (fun r hr => show 0 ≤ ‖toYCoord d e k r.val‖ +
      ‖fromYCoord d e k r.val‖ by positivity) (Finset.mem_univ (⟨i,hi⟩ : Fin k))
    dsimp [bound]
    nlinarith [norm_nonneg (fromYCoord d e k i)]
  · have hb : ‖toYCoord d e k i‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖toYCoord d e k i x‖ ≤ 1 * ‖x‖
      simp only [toYCoord, dif_neg hi]
      change ‖tailIsometry d k i hi x‖ ≤ 1 * ‖x‖
      rw [LinearIsometryEquiv.norm_map, one_mul]
    dsimp [bound]
    linarith

theorem norm_fromYCoord_le_bound (i : ℕ) : ‖fromYCoord d e k i‖ ≤ bound d e k := by
  have hs : 0 ≤ ∑ r : Fin k, (‖toYCoord d e k r.val‖ + ‖fromYCoord d e k r.val‖) :=
    Finset.sum_nonneg (fun r hr => by positivity)
  by_cases hi : i < k
  · have hf := Finset.single_le_sum (fun r hr => show 0 ≤ ‖toYCoord d e k r.val‖ +
      ‖fromYCoord d e k r.val‖ by positivity) (Finset.mem_univ (⟨i,hi⟩ : Fin k))
    dsimp [bound]
    nlinarith [norm_nonneg (toYCoord d e k i)]
  · have hb : ‖fromYCoord d e k i‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖fromYCoord d e k i x‖ ≤ 1 * ‖x‖
      simp only [fromYCoord, dif_neg hi]
      change ‖(tailIsometry d k i hi).symm x‖ ≤ 1 * ‖x‖
      rw [LinearIsometryEquiv.norm_map, one_mul]
    dsimp [bound]
    linarith

def toY : d.Z k →L[ℝ] G d := L1Linear.continuousLinearMap (toYCoord d e k) (bound d e k) (norm_toYCoord_le_bound d e k)
def fromY : G d →L[ℝ] d.Z k := L1Linear.continuousLinearMap (fromYCoord d e k) (bound d e k) (norm_fromYCoord_le_bound d e k)
def toH : d.Z k →L[ℝ] D k :=
  ContinuousLinearMap.pi (fun r => (toHCoord d e k r).comp (lp.evalCLM ℝ (fun i => (d.mixed k i).Carrier) 1 r.val))
def fromH : D k →L[ℝ] d.Z k :=
  ∑ r : Fin k, (lp.singleContinuousLinearMap ℝ (fun i => (d.mixed k i).Carrier) 1 r.val).comp
    ((fromHCoord d e k r).comp (L1FiniteHead.finiteEval (fun _ : ℕ => C0L2) k r))

theorem fromH_apply (v : D k) (i : ℕ) :
    fromH d e k v i = if hi : i < k then fromHCoord d e k ⟨i,hi⟩ (v ⟨i,hi⟩) else 0 := by
  classical
  change (lp.evalCLM ℝ (fun i => (d.mixed k i).Carrier) 1 i) (fromH d e k v) = _
  simp only [fromH, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rw [map_sum]
  simp only [lp.singleContinuousLinearMap_apply, L1FiniteHead.finiteEval]
  by_cases hi : i < k
  · rw [dif_pos hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin k)]
    · exact lp.single_apply_self 1 i _
    · intro r hr hne
      apply lp.single_apply_ne 1 r.val _
      intro hir
      exact hne (Fin.ext hir.symm)
    · intro h; exact (h (Finset.mem_univ _)).elim
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro r hr
    apply lp.single_apply_ne 1 r.val _
    intro hir
    exact hi (hir.symm ▸ r.isLt)

def equiv : d.Z k ≃L[ℝ] (G d × D k) where
  toLinearEquiv := {
    toFun := fun x => (toY d e k x, toH d e k x)
    invFun := fun z => fromY d e k z.1 + fromH d e k z.2
    left_inv := by
      intro x; apply lp.ext; funext i
      change fromYCoord d e k i (toYCoord d e k i (x i)) + fromH d e k (toH d e k x) i = x i
      rw [fromH_apply]
      split_ifs with hi
      · exact recover_head d e k ⟨i,hi⟩ (x i)
      · rw [add_zero]; exact recover_tail d e k i hi (x i)
    right_inv := by
      intro z; apply Prod.ext
      · apply lp.ext; funext i
        change toYCoord d e k i (fromYCoord d e k i (z.1 i) + fromH d e k z.2 i) = z.1 i
        rw [map_add, toYCoord_fromYCoord, fromH_apply]
        split_ifs with hi
        · have hz : toYCoord d e k i (fromHCoord d e k ⟨i, hi⟩ (z.2 ⟨i, hi⟩)) = 0 :=
            toYCoord_fromHCoord d e k ⟨i, hi⟩ (z.2 ⟨i, hi⟩)
          exact (congrArg (fun v => z.1 i + v) hz).trans (add_zero _)
        · rw [map_zero, add_zero]
      · funext r
        change toHCoord d e k r (fromYCoord d e k r.val (z.1 r.val) + fromH d e k z.2 r.val) = z.2 r
        rw [map_add, toHCoord_fromYCoord, fromH_apply, dif_pos r.isLt, toHCoord_fromHCoord, zero_add]
    map_add' := by intro x y; apply Prod.ext <;> exact map_add _ _ _
    map_smul' := by intro r x; apply Prod.ext <;> exact map_smul _ _ _ }
  continuous_toFun := (toY d e k).continuous.prodMk (toH d e k).continuous
  continuous_invFun := ((fromY d e k).continuous.comp continuous_fst).add
    ((fromH d e k).continuous.comp continuous_snd)

end RowSplitting
end BanachGeometry
