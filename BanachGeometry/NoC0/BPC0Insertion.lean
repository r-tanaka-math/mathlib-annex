import BanachGeometry.NoC0.BasisSeries

/-! Inserting scalar c₀ coordinates at an injective sequence of positions.
Membership is proved using finite exceptional images. No series in the
target Banach space is constructed.
Execution evidence is recorded in the external receipts. -/
noncomputable section
open Filter
namespace BanachGeometry
namespace BP
variable (s : ℕ → ℕ) (hs : Function.Injective s)

def insertValue (a : ScalarC0) (i : ℕ) : ℝ := by
  classical
  exact if h : ∃ j, s j = i then a (Classical.choose h) else 0

include hs in
@[simp] theorem insertValue_apply_image (a : ScalarC0) (j : ℕ) : insertValue s a (s j) = a j := by
  classical
  have h : ∃ k, s k = s j := ⟨j,rfl⟩
  rw [insertValue,dif_pos h]
  rw [hs (Classical.choose_spec h)]

theorem insertValue_eq_zero_of_not_mem_range (a : ScalarC0) (i : ℕ) (hi : ¬ ∃ j, s j = i) :
    insertValue s a i = 0 := by
  classical
  exact dif_neg hi

theorem norm_insertValue_le (a : ScalarC0) (i : ℕ) : ‖insertValue s a i‖ ≤ ‖a‖ := by
  classical
  unfold insertValue
  split_ifs with h
  · exact CanonicalSequences.norm_apply_scalar_le a (Classical.choose h)
  · simpa only [norm_zero] using norm_nonneg a

theorem tendsto_norm_insertValue_cofinite (a : ScalarC0) :
    Tendsto (fun i => ‖insertValue s a i‖) cofinite (nhds 0) := by
  classical
  let x := (C0Sum.homogeneousLinearIsometryEquiv ℝ).symm a
  have hx := x.null_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hx.eventually (eventually_lt_nhds hε))
  filter_upwards [((Finset.range N).image s).eventually_cofinite_notMem] with i hi
  change dist ‖insertValue s a i‖ 0 < ε
  rw [dist_zero_right,Real.norm_of_nonneg (norm_nonneg _)]
  unfold insertValue
  split_ifs with h
  · let j := Classical.choose h
    have hj : s j = i := Classical.choose_spec h
    have hjN : N ≤ j := by
      by_contra hbad
      apply hi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),hj⟩
    exact hN j hjN
  · simpa only [norm_zero] using hε

def rawInsert (a : ScalarC0) : C0Sum (fun _ : ℕ => ℝ) :=
  C0Sum.ofBound (insertValue s a) (tendsto_norm_insertValue_cofinite s a) ‖a‖ (norm_insertValue_le s a)

include hs in
theorem norm_rawInsert (a : ScalarC0) : ‖rawInsert s a‖ = ‖a‖ := by
  apply le_antisymm (C0Sum.norm_le (norm_nonneg _) (norm_insertValue_le s a))
  let e := C0Sum.homogeneousLinearIsometryEquiv ℝ
  have h : ‖e.symm a‖ ≤ ‖rawInsert s a‖ := by
    apply C0Sum.norm_le (norm_nonneg _)
    intro j
    change ‖a j‖ ≤ ‖rawInsert s a‖
    rw [← insertValue_apply_image s hs a j]
    exact (rawInsert s a).norm_apply_le (s j)
  simpa only [e.symm.norm_map] using h

def rawInsertCLM : ScalarC0 →L[ℝ] C0Sum (fun _ : ℕ => ℝ) :=
  ({ toFun := rawInsert s
     map_add' := by
       classical
       intro a b; apply C0Sum.ext; intro i
       change insertValue s (a+b) i = insertValue s a i + insertValue s b i
       unfold insertValue
       split_ifs
       · rfl
       · simp
     map_smul' := by
       classical
       intro r a; apply C0Sum.ext; intro i
       change insertValue s (r • a) i = r • insertValue s a i
       unfold insertValue
       split_ifs <;> simp } : ScalarC0 →ₗ[ℝ] C0Sum (fun _ : ℕ => ℝ)).mkContinuous 1
    (by intro a; simpa only [one_mul] using C0Sum.norm_le (norm_nonneg a) (norm_insertValue_le s a))

def insertCLM : ScalarC0 →L[ℝ] ScalarC0 :=
  (C0Sum.homogeneousLinearIsometryEquiv ℝ).toLinearIsometry.toContinuousLinearMap.comp
    (rawInsertCLM s)

@[simp] theorem insertCLM_apply (a : ScalarC0) (i : ℕ) : insertCLM s a i = insertValue s a i := rfl
include hs in
@[simp] theorem insertCLM_apply_image (a : ScalarC0) (j : ℕ) : insertCLM s a (s j) = a j :=
  insertValue_apply_image s hs a j

include hs in
theorem norm_insertCLM (a : ScalarC0) : ‖insertCLM s a‖ = ‖a‖ := by
  change ‖(C0Sum.homogeneousLinearIsometryEquiv ℝ) (rawInsert s a)‖ = ‖a‖
  rw [LinearIsometryEquiv.norm_map,norm_rawInsert s hs]

include hs in
theorem insertCLM_scalarBasis (n : ℕ) :
    insertCLM s (CanonicalSequences.scalarBasis n) = CanonicalSequences.scalarBasis (s n) := by
  classical
  apply ZeroAtInftyContinuousMap.ext
  intro i
  by_cases h : ∃ j, s j = i
  · obtain ⟨j,rfl⟩ := h
    rw [insertCLM_apply_image s hs]
    by_cases hj : j = n
    · subst j
      change C0Sum.single (E := fun _ : ℕ => ℝ) n (1 : ℝ) n =
        C0Sum.single (E := fun _ : ℕ => ℝ) (s n) (1 : ℝ) (s n)
      rw [C0Sum.single_apply_self, C0Sum.single_apply_self]
    · have hsj : s j ≠ s n := fun h => hj (hs h)
      change C0Sum.single (E := fun _ : ℕ => ℝ) n (1 : ℝ) j =
        C0Sum.single (E := fun _ : ℕ => ℝ) (s n) (1 : ℝ) (s j)
      rw [C0Sum.single_apply_ne n 1 hj,C0Sum.single_apply_ne (s n) 1 hsj]
  · rw [insertCLM_apply,insertValue_eq_zero_of_not_mem_range s _ _ h]
    have hi : i ≠ s n := by intro hi; exact h ⟨n,hi.symm⟩
    change (0 : ℝ) = C0Sum.single (E := fun _ : ℕ => ℝ) (s n) (1 : ℝ) i
    rw [C0Sum.single_apply_ne (s n) 1 hi]

theorem scalarHead_eq_sum (N : ℕ) (a : ScalarC0) :
    CanonicalSequences.scalarHead N a = ∑ j ∈ Finset.range N, a j • CanonicalSequences.scalarBasis j := by
  change (C0Sum.homogeneousLinearIsometryEquiv ℝ)
    (∑ j ∈ Finset.range N, C0Sum.single j (a j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : C0Sum.single (E := fun _ : ℕ => ℝ) j (a j) =
      a j • C0Sum.single j (1 : ℝ) := by
    have h := (C0Sum.singleLinearIsometry (E := fun _ : ℕ => ℝ) j).map_smul (a j) 1
    change C0Sum.single (E := fun _ : ℕ => ℝ) j (a j • (1 : ℝ)) =
      a j • C0Sum.single j (1 : ℝ) at h
    simpa only [smul_eq_mul,mul_one] using h
  rw [he,map_smul]
  rfl

include hs in
theorem insertCLM_scalarHead (N : ℕ) (a : ScalarC0) :
    insertCLM s (CanonicalSequences.scalarHead N a) =
      ∑ j ∈ Finset.range N, a j • CanonicalSequences.scalarBasis (s j) := by
  rw [scalarHead_eq_sum,map_sum]
  simp only [map_smul,insertCLM_scalarBasis s hs]

theorem norm_scalarHead_le_of_bound (N : ℕ) (a : ScalarC0) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ j ∈ Finset.range N, |a j| ≤ M) : ‖CanonicalSequences.scalarHead N a‖ ≤ M := by
  change ‖(C0Sum.homogeneousLinearIsometryEquiv ℝ) (C0Sum.head _ N _)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  apply C0Sum.norm_le hM
  intro j
  rw [C0Sum.head_apply]
  split_ifs with hj
  · exact h j (Finset.mem_range.mpr hj)
  · simpa only [norm_zero] using hM

end BP
end BanachGeometry
