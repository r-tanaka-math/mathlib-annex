import BanachGeometry.Complemented.FiniteDual
import BanachGeometry.Complemented.RowSplitting
import Mathlib.Analysis.Normed.Group.Constructions

/-! Repetitions in finite families and finite products of Y-only rows.
The proof uses simultaneous ℓ₁ tails and a finite grid of repeated Y_i,
not a uniform splitting bound or a replacement of the row norms. -/
noncomputable section
open Filter TopologicalSpace
namespace BanachGeometry
namespace FiniteRows

def reindexIsometry {I J : Type*} [Fintype I] [Fintype J]
    (V : I → Type*) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    (e : I ≃ J) : (∀ i, V i) →ₗᵢ[ℝ] (∀ j, V (e.symm j)) where
  toFun z j := z (e.symm j)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  norm_map' z := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
      intro j; exact norm_le_pi_norm z (e.symm j)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      change ‖z i‖ ≤ ‖fun j => z (e.symm j)‖
      have h := norm_le_pi_norm (fun j => z (e.symm j)) (e i)
      have he : ‖z (e.symm (e i))‖ = ‖z i‖ := congrArg (fun j => ‖z j‖) (e.symm_apply_apply i)
      exact he.symm.le.trans h

theorem noCopy_finite_family (d : AlmostIsometricFamily) (h4 : d.ExcludesFiniteSumCopy)
    (I : Type*) [Fintype I] (indices : I → ℕ) :
    ¬ ContainsLinearCopy C0L2 (∀ i, (d.Y (indices i)).Carrier) := by
  classical
  rintro ⟨T, a, ha, hT⟩
  let e := Fintype.equivFin I
  let R := reindexIsometry (fun i => (d.Y (indices i)).Carrier) e
  apply h4 (Fintype.card I) (fun r => indices (e.symm r))
  refine ⟨R.toContinuousLinearMap.comp T, a, ha, ?_⟩
  intro x
  change a * ‖x‖ ≤ ‖R (T x)‖
  rw [R.norm_map]
  exact hT x

theorem noCopy_product_Yrows (d : AlmostIsometricFamily) (h4 : d.ExcludesFiniteSumCopy) (q : ℕ) :
    ¬ ContainsLinearCopy C0L2 (Fin q → RowSplitting.G d) := by
  letI : SeparableSpace (C0L2 →L[ℝ] ℝ) := separableSpace_dual_c0L2
  rintro ⟨T, a, ha, hT⟩
  let V := fun i => (d.Y i).Carrier
  let Tr := fun r : Fin q => (ContinuousLinearMap.proj r).comp T
  have he : ∀ᶠ m in atTop, ∀ r ∈ (Finset.univ : Finset (Fin q)),
      ‖(L1Tails.tail V m).comp (Tr r)‖ < a / 2 := by
    apply (Filter.eventually_all_finset _).mpr
    intro r hr
    exact (L1Tails.tendsto_opNorm_tail_comp V (Tr r)).eventually (eventually_lt_nhds (half_pos ha))
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 he
  let F := L1FiniteHead.fromPi V m
  let U : C0L2 →L[ℝ] (∀ s : Fin q × Fin m, V s.2.val) :=
    ContinuousLinearMap.pi (fun s => (lp.evalCLM ℝ V 1 s.2.val).comp (Tr s.1))
  apply noCopy_finite_family d h4 (Fin q × Fin m) (fun s => s.2.val)
  have hden : 0 < ‖F‖ + 1 := by positivity
  refine ⟨U, (a/2)/(‖F‖+1), div_pos (half_pos ha) hden, ?_⟩
  intro x
  have htail (r : Fin q) : ‖L1Tails.tail V m (Tr r x)‖ ≤ (a/2) * ‖x‖ :=
    (((L1Tails.tail V m).comp (Tr r)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hm m le_rfl r (Finset.mem_univ r)).le (norm_nonneg x))
  have hhead (r : Fin q) : ‖L1Tails.head V m (Tr r x)‖ ≤ ‖F‖ * ‖U x‖ := by
    rw [← L1FiniteHead.fromPi_firstPi V m (Tr r x)]
    apply (F.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg F)
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro s
    exact norm_le_pi_norm (U x) (r,s)
  have hTx : ‖T x‖ ≤ ‖F‖ * ‖U x‖ + (a/2) * ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro r
    have hsplit : Tr r x = L1Tails.head V m (Tr r x) + L1Tails.tail V m (Tr r x) := by
      rw [L1Tails.tail_eq_sub_head]; abel
    change ‖Tr r x‖ ≤ _
    conv_lhs => rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (hhead r) (htail r))
  have hlo := hT x
  calc
    ((a/2)/(‖F‖+1)) * ‖x‖ = ((a/2) * ‖x‖)/(‖F‖+1) := by ring
    _ ≤ ‖U x‖ := (div_le_iff₀ hden).mpr (by nlinarith [norm_nonneg (U x)])

end FiniteRows
end BanachGeometry
