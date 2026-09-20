import MathlibAnnex.Analysis.Normed.Module.EquivalentSeminorm.Topology
import MathlibAnnex.LinearAlgebra.Matrix.VolumeScaledMaximalMinor
import MathlibAnnex.Analysis.Convex.CompactHull

/-!
# The symmetric convex body of volume-scaled maximal minors

The generators consist exactly of both signs of every model contraction's
scaled maximal-minor vector. The body is their real convex hull.
-/

noncomputable section

namespace MathlibAnnex.PluckerBody

open Set Matrix

/-- Both signs of the volume-scaled minors of each model contraction. -/
def generators {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) (N : ℕ) :
    Set (Matrix.MaximalMinorIndex n (Fin N) → ℝ) :=
  {z | ∃ A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ),
    M.IsContraction A ∧
      (z = Matrix.ballVolumeScaledMaximalMinors M A ∨
        z = -Matrix.ballVolumeScaledMaximalMinors M A)}

/-- The convex hull of all signed model-contraction generators. -/
def body {n : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) (N : ℕ) :
    Set (Matrix.MaximalMinorIndex n (Fin N) → ℝ) := convexHull ℝ (generators M N)

theorem generators_nonempty {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    (generators M N).Nonempty := by
  exact ⟨Matrix.ballVolumeScaledMaximalMinors M 0, 0, M.isContraction_zero, Or.inl rfl⟩

theorem generators_neg {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    {z : Matrix.MaximalMinorIndex n (Fin N) → ℝ} (hz : z ∈ generators M N) :
    -z ∈ generators M N := by
  rcases hz with ⟨A, hA, hpos | hneg⟩
  · refine ⟨A, hA, Or.inr ?_⟩; simp [hpos]
  · refine ⟨A, hA, Or.inl ?_⟩; simp [hneg]

theorem body_neg {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ))
    {z : Matrix.MaximalMinorIndex n (Fin N) → ℝ} (hz : z ∈ body M N) :
    -z ∈ body M N := by
  change z ∈ convexHull ℝ (generators M N) at hz
  have hsub : generators M N ⊆ -body M N := by
    intro w hw
    exact Set.mem_neg.mpr (subset_convexHull ℝ _ (generators_neg M hw))
  have hzneg : z ∈ -body M N :=
    convexHull_min hsub (convex_convexHull ℝ (generators M N)).neg hz
  exact Set.mem_neg.mp hzneg

theorem generators_eq_image_union {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    generators M N =
      Matrix.ballVolumeScaledMaximalMinors M '' M.contractionSet (Fin N → ℝ) ∪
      (fun z : Matrix.MaximalMinorIndex n (Fin N) → ℝ => -z) ''
        (Matrix.ballVolumeScaledMaximalMinors M '' M.contractionSet (Fin N → ℝ)) := by
  ext z
  constructor
  · rintro ⟨A, hA, rfl | rfl⟩
    · exact Or.inl ⟨A, hA, rfl⟩
    · exact Or.inr ⟨Matrix.ballVolumeScaledMaximalMinors M A, ⟨A, hA, rfl⟩, rfl⟩
  · rintro (⟨A, hA, rfl⟩ | ⟨w, ⟨A, hA, rfl⟩, rfl⟩)
    · exact ⟨A, hA, Or.inl rfl⟩
    · exact ⟨A, hA, Or.inr rfl⟩

/-- The generator set is compact at every pair of finite dimensions. -/
theorem isCompact_generators {n N : ℕ} (M : EquivalentSeminorm (Fin n → ℝ)) :
    IsCompact (generators M N) := by
  rw [generators_eq_image_union]
  have hclosed : IsClosed (M.contractionSet (Fin N → ℝ)) := by
    have heq : M.contractionSet (Fin N → ℝ) =
        ⋂ x : Fin n → ℝ, {A : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ) | ‖A x‖ ≤ M.p x} := by
      ext A
      simp [EquivalentSeminorm.contractionSet, EquivalentSeminorm.IsContraction]
    rw [heq]
    apply isClosed_iInter
    intro x
    apply isClosed_le _ continuous_const
    fun_prop
  have hbounded : Bornology.IsBounded (M.contractionSet (Fin N → ℝ)) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ))).2 ?_
    refine ⟨M.upper, ?_⟩
    intro A hA
    have hnorm : ‖A‖ ≤ M.upper :=
      ContinuousLinearMap.opNorm_le_bound A M.upper_pos.le (fun x => (hA x).trans (M.le_upper x))
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  have hC : IsCompact (M.contractionSet (Fin N → ℝ)) :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbounded
  have hpos := hC.image (Matrix.continuous_ballVolumeScaledMaximalMinors M)
  exact hpos.union (hpos.image continuous_neg)

end MathlibAnnex.PluckerBody
