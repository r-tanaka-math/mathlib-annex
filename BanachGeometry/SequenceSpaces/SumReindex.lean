import BanachGeometry.SequenceSpaces.C0Sum
import BanachGeometry.SequenceSpaces.L1Map
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped ENNReal

/-! Dependent permutations of the actual ℓ₁ and c₀ carriers. Coordinate
spaces move together with their indices; no heterogeneous vectors are added.
Both maps are linear isometries.
Execution evidence is recorded in the external receipts. -/
noncomputable section
namespace BanachGeometry
namespace SumReindex
variable {I J : Type*} (V : J → Type*)
    [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)] (r : I ≃ J)

def l1 : L1Sum (fun i => V (r i)) ≃ₗᵢ[ℝ] L1Sum V := by
  classical
  let p : (∀ i, V (r i)) ≃ (∀ j, V j) := r.piCongr (fun _ => Equiv.refl _)
  have hp (x : ∀ i, V (r i)) (i : I) : p x (r i) = x i :=
    Equiv.piCongr_apply_apply _ _ _ _
  have hps (y : ∀ j, V j) (i : I) : p.symm y i = y (r i) := rfl
  let f : L1Sum (fun i => V (r i)) → L1Sum V := fun x => ⟨p x, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    have hs : Summable (fun j => ‖p x j‖) := r.summable_iff.mp (by
      simpa only [Function.comp_def, hp] using l1_summable x)
    simpa only [ENNReal.toReal_one, Real.rpow_one] using hs⟩
  let g : L1Sum V → L1Sum (fun i => V (r i)) := fun y => ⟨p.symm y, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    have hs := r.summable_iff.mpr (l1_summable y)
    simpa only [Function.comp_def, hps, ENNReal.toReal_one, Real.rpow_one] using hs⟩
  refine
    { toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_
      norm_map' := ?_ }
  · intro x y; apply lp.ext; funext j
    obtain ⟨i,rfl⟩ := r.surjective j
    change p (x+y) (r i) = p x (r i) + p y (r i)
    simp only [hp]; rfl
  · intro a x; apply lp.ext; funext j
    obtain ⟨i,rfl⟩ := r.surjective j
    change p (a • x) (r i) = a • p x (r i)
    simp only [hp]; rfl
  · intro x; apply lp.ext; exact congrArg (fun h => h) (p.symm_apply_apply x)
  · intro y; apply lp.ext; exact congrArg (fun h => h) (p.apply_symm_apply y)
  · intro x
    change ‖f x‖ = ‖x‖
    rw [l1_norm_eq_tsum, l1_norm_eq_tsum]
    change (∑' j, ‖p x j‖) = ∑' i, ‖x i‖
    rw [← r.tsum_eq (fun j => ‖p x j‖)]
    exact tsum_congr (fun i => congrArg norm (hp x i))

def c0 : C0Sum (fun i => V (r i)) ≃ₗᵢ[ℝ] C0Sum V := by
  let e : ∀ i, PointedBiLip (V (r i)) (V (r i)) 1 := fun i => PointedBiLip.refl _ 1 le_rfl
  let p := c0ReindexBiLip V r 1 zero_le_one e
  have hp (x : C0Sum (fun i => V (r i))) (i : I) : p.equiv x (r i) = x i :=
    c0ReindexBiLip_apply_index V r 1 zero_le_one e x i
  refine { toEquiv := p.equiv, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro x y; apply C0Sum.ext; intro j
    obtain ⟨i,rfl⟩ := r.surjective j
    change p.equiv (x + y) (r i) = p.equiv x (r i) + p.equiv y (r i)
    rw [hp, hp, hp]
    rfl
  · intro a x; apply C0Sum.ext; intro j
    obtain ⟨i,rfl⟩ := r.surjective j
    change p.equiv (a • x) (r i) = a • p.equiv x (r i)
    rw [hp, hp]
    rfl
  · intro x
    change ‖p.equiv x‖ = ‖x‖
    apply le_antisymm
    · simpa only [one_mul] using p.norm_le x
    · have h := p.symm_norm_le (p.equiv x)
      simpa only [p.equiv.symm_apply_apply, one_mul] using h

@[simp] theorem l1_apply_index (x : L1Sum (fun i => V (r i))) (i : I) :
    l1 V r x (r i) = x i := by
  exact Equiv.piCongr_apply_apply _ _ _ _

@[simp] theorem l1_symm_apply (y : L1Sum V) (i : I) : (l1 V r).symm y i = y (r i) := rfl

@[simp] theorem c0_apply_index (x : C0Sum (fun i => V (r i))) (i : I) :
    c0 V r x (r i) = x i := by
  exact c0ReindexBiLip_apply_index V r 1 zero_le_one
    (fun i => PointedBiLip.refl _ 1 le_rfl) x i

@[simp] theorem c0_symm_apply (y : C0Sum V) (i : I) : (c0 V r).symm y i = y (r i) := rfl

end SumReindex
end BanachGeometry
