import BanachGeometry.AlmostIsometric.PointedBiLip
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Topology.Instances.Nat

/-!
# A heterogeneous c₀ sum

This is the norm-null submodule of `lp E ∞`, with the inherited supremum
norm. The vanishing condition is part of the type; the ambient ℓ∞ space
is never identified with c₀. `cofinite` permits reindexing by any equivalence;
for natural indices it equals `atTop`.
-/

noncomputable section
open Filter
open scoped ENNReal
namespace BanachGeometry

universe u v w
variable {ι : Type u} {κ : Type v}
variable (E : ι → Type w) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]

def c0Submodule : Submodule ℝ (lp E ∞) where
  carrier := {x | Tendsto (fun i => ‖x i‖) cofinite (nhds 0)}
  zero_mem' := by simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) _ _)
  add_mem' := by
    intro x y hx hy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hx.add hy)
    · intro i; exact norm_nonneg _
    · intro i; exact norm_add_le _ _
  smul_mem' := by
    intro a x hx
    change Tendsto (fun i => ‖(a • x) i‖) cofinite (nhds 0)
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, mul_zero] using
      (tendsto_const_nhds.mul hx :
        Tendsto (fun i => ‖a‖ * ‖x i‖) cofinite (nhds (‖a‖ * 0)))

/-- Heterogeneous c₀ sum with its single inherited norm instance. -/
abbrev C0Sum := ↥(c0Submodule E)

namespace C0Sum
variable {E}

instance : CoeFun (C0Sum E) (fun _ => ∀ i, E i) := ⟨fun x i => x.1 i⟩

@[ext] theorem ext {x y : C0Sum E} (h : ∀ i, x i = y i) : x = y := by
  apply Subtype.ext
  apply lp.ext
  exact funext h

@[simp] theorem zero_apply (i : ι) : (0 : C0Sum E) i = 0 := rfl
@[simp] theorem add_apply (x y : C0Sum E) (i : ι) : (x + y) i = x i + y i := rfl
@[simp] theorem sub_apply (x y : C0Sum E) (i : ι) : (x - y) i = x i - y i := rfl
@[simp] theorem smul_apply (a : ℝ) (x : C0Sum E) (i : ι) : (a • x) i = a • x i := rfl

theorem null (x : C0Sum E) : Tendsto (fun i => ‖x i‖) cofinite (nhds 0) := x.2

theorem norm_apply_le (x : C0Sum E) (i : ι) : ‖x i‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.1 i

theorem norm_le {x : C0Sum E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖x i‖ ≤ C) : ‖x‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

theorem norm_eq_iSup (x : C0Sum E) : ‖x‖ = ⨆ i, ‖x i‖ :=
  lp.norm_eq_ciSup x.1

/-- Build an element from a norm-null family and an explicit bound. -/
def ofBound (f : ∀ i, E i) (hnull : Tendsto (fun i => ‖f i‖) cofinite (nhds 0))
    (C : ℝ) (hbound : ∀ i, ‖f i‖ ≤ C) : C0Sum E :=
  ⟨⟨f, memℓp_infty ⟨C, by rintro _ ⟨i, rfl⟩; exact hbound i⟩⟩, hnull⟩

@[simp] theorem ofBound_apply (f : ∀ i, E i)
    (hnull : Tendsto (fun i => ‖f i‖) cofinite (nhds 0))
    (C : ℝ) (hbound : ∀ i, ‖f i‖ ≤ C) (i : ι) :
    ofBound f hnull C hbound i = f i := rfl

/-- The defining condition is genuinely norm convergence to zero for sequences. -/
theorem null_atTop {V : ℕ → Type*} [∀ n, NormedAddCommGroup (V n)]
    [∀ n, NormedSpace ℝ (V n)] (x : C0Sum V) :
    Tendsto (fun n => ‖x n‖) atTop (nhds 0) := by
  simpa only [Nat.cofinite_eq_atTop] using x.null

end C0Sum

section Reindex
variable {E}
variable (F : κ → Type*) [∀ k, NormedAddCommGroup (F k)]
    [∀ k, NormedSpace ℝ (F k)]

/-- Uniformly bounded pointed coordinate maps and a permutation preserve
the c₀ condition. This is the outer-sum step used in insertion, including
both directions and their quantitative estimates. -/
def c0ReindexBiLip (r : ι ≃ κ) (C : ℝ) (hC : 0 ≤ C)
    (e : ∀ i, PointedBiLip (E i) (F (r i)) C) :
    PointedBiLip (C0Sum E) (C0Sum F) C := by
  classical
  let p : (∀ i, E i) ≃ (∀ k, F k) := r.piCongr (fun i => (e i).equiv)
  have hp (f : ∀ i, E i) (i : ι) : p f (r i) = (e i).equiv (f i) := by
    exact Equiv.piCongr_apply_apply _ _ _ _
  have hps (g : ∀ k, F k) (i : ι) : p.symm g i = (e i).equiv.symm (g (r i)) := rfl
  have fnull (x : C0Sum E) : Tendsto (fun k => ‖p x k‖) cofinite (nhds 0) := by
    have ht : Tendsto (fun i => ‖p x (r i)‖) cofinite (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using (tendsto_const_nhds.mul x.null :
          Tendsto (fun i => C * ‖x i‖) cofinite (nhds (C * 0))))
      · intro i; exact norm_nonneg _
      · intro i
        exact (congrArg norm (hp (fun j => x j) i)).le.trans ((e i).norm_le _)
    exact (ht.comp r.symm.injective.tendsto_cofinite).congr'
      (Eventually.of_forall fun k => congrArg (fun j => ‖p (fun i => x i) j‖)
        (r.apply_symm_apply k))
  have gnull (y : C0Sum F) : Tendsto (fun i => ‖p.symm y i‖) cofinite (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (tendsto_const_nhds.mul (y.null.comp r.injective.tendsto_cofinite) :
        Tendsto (fun i => C * ‖y (r i)‖) cofinite (nhds (C * 0))))
    · intro i; exact norm_nonneg _
    · intro i
      exact (congrArg norm (hps (fun k => y k) i)).le.trans ((e i).symm_norm_le _)
  let f : C0Sum E → C0Sum F := fun x => C0Sum.ofBound (p x) (fnull x) (C * ‖x‖) (by
    intro k
    obtain ⟨i, rfl⟩ := r.surjective k
    rw [hp]
    exact ((e i).norm_le _).trans
      (mul_le_mul_of_nonneg_left (x.norm_apply_le i) hC))
  let g : C0Sum F → C0Sum E := fun y => C0Sum.ofBound (p.symm y) (gnull y) (C * ‖y‖) (by
    intro i
    rw [hps]
    exact ((e i).symm_norm_le _).trans
      (mul_le_mul_of_nonneg_left (y.norm_apply_le (r i)) hC))
  refine
    { equiv :=
        { toFun := f
          invFun := g
          left_inv := ?_
          right_inv := ?_ }
      zero_eq := ?_
      forward := ?_
      backward := ?_ }
  · intro x; apply C0Sum.ext; intro i
    change p.symm (p x) i = x i
    exact congrFun (p.symm_apply_apply x) i
  · intro y; apply C0Sum.ext; intro k
    change p (p.symm y) k = y k
    exact congrFun (p.apply_symm_apply y) k
  · apply C0Sum.ext; intro k
    obtain ⟨i, rfl⟩ := r.surjective k
    change p (fun i => 0) (r i) = 0
    rw [hp]; exact (e i).zero_eq
  · intro x y
    apply C0Sum.norm_le (mul_nonneg hC (norm_nonneg _))
    intro k
    obtain ⟨i, rfl⟩ := r.surjective k
    change ‖p x (r i) - p y (r i)‖ ≤ C * ‖x - y‖
    rw [hp, hp]
    exact ((e i).forward _ _).trans
      (mul_le_mul_of_nonneg_left ((x - y).norm_apply_le i) hC)
  · intro x y
    apply C0Sum.norm_le (mul_nonneg hC (norm_nonneg _))
    intro i
    change ‖p.symm x i - p.symm y i‖ ≤ C * ‖x - y‖
    rw [hps, hps]
    exact ((e i).backward _ _).trans
      (mul_le_mul_of_nonneg_left ((x - y).norm_apply_le (r i)) hC)

/-- Coordinate formula without any heterogeneous transport ambiguity. -/
theorem c0ReindexBiLip_apply_index (r : ι ≃ κ) (C : ℝ) (hC : 0 ≤ C)
    (e : ∀ i, PointedBiLip (E i) (F (r i)) C) (x : C0Sum E) (i : ι) :
    (c0ReindexBiLip F r C hC e).equiv x (r i) = (e i).equiv (x i) := by
  change (r.piCongr (fun i => (e i).equiv)) x (r i) = (e i).equiv (x i)
  exact Equiv.piCongr_apply_apply _ _ _ _

theorem c0ReindexBiLip_symm_apply (r : ι ≃ κ) (C : ℝ) (hC : 0 ≤ C)
    (e : ∀ i, PointedBiLip (E i) (F (r i)) C) (y : C0Sum F) (i : ι) :
    (c0ReindexBiLip F r C hC e).equiv.symm y i = (e i).equiv.symm (y (r i)) := rfl

end Reindex
end BanachGeometry
