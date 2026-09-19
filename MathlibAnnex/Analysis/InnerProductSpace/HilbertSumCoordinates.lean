import MathlibAnnex.Analysis.InnerProductSpace.HilbertSum
import MathlibAnnex.Analysis.InnerProductSpace.RankOneCompletion

/-!
# Coordinate maps and inter-block links on dependent Hilbert sums

The maps here retain the arbitrary index type and dependent fibers of
Mathlib's `lp` model.  In particular, `interblockRankOne` is an off-diagonal
operator between two displayed coordinates, not a fiberwise diagonal map.
-/

set_option autoImplicit false

open scoped ENNReal lp InnerProduct

namespace MathlibAnnex.Analysis.InnerProductSpace

universe u v

variable {I : Type u} {H : I → Type v}
variable [DecidableEq I]
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Isometric inclusion of one fiber into the dependent Hilbert sum. -/
noncomputable def coordinateEmbedding (i : I) : H i →L[ℂ] HilbertSum H :=
  by
    classical
    exact lp.singleContinuousLinearMap ℂ H 2 i

@[simp]
theorem coordinateEmbedding_apply (i : I) (x : H i) :
    coordinateEmbedding i x = lp.single 2 i x :=
  by
    classical
    rfl

/-- Bounded evaluation at one coordinate of the dependent Hilbert sum. -/
noncomputable def coordinateProjection (i : I) : HilbertSum H →L[ℂ] H i :=
  lp.evalCLM ℂ H 2 i

@[simp]
theorem coordinateProjection_apply (i : I) (x : HilbertSum H) :
    coordinateProjection i x = x i :=
  rfl

theorem norm_coordinateEmbedding (i : I) (x : H i) :
    ‖coordinateEmbedding i x‖ = ‖x‖ := by
  classical
  exact lp.norm_single (p := 2) (by norm_num) i x

/-- Different coordinate copies are orthogonal. -/
theorem inner_coordinateEmbedding_eq_zero {i j : I} (hij : i ≠ j)
    (x : H i) (y : H j) :
    inner ℂ (coordinateEmbedding i x) (coordinateEmbedding j y) = 0 := by
  classical
  rw [coordinateEmbedding_apply, lp.inner_single_left]
  simp [lp.coeFn_single, hij]

/-- The actual rank-one operator from coordinate `j` to coordinate `i`. -/
noncomputable def interblockRankOne (i j : I) (a : H i) (b : H j) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  InnerProductSpace.rankOne ℂ (coordinateEmbedding i a) (coordinateEmbedding j b)

/-- An inter-block rank-one link sends its selected unit source to the
selected target. -/
theorem interblockRankOne_apply_source (i j : I) (a : H i) (b : H j)
    (hb : ‖b‖ = 1) :
    interblockRankOne i j a b (coordinateEmbedding j b) =
      coordinateEmbedding i a := by
  have hnorm : ‖coordinateEmbedding j b‖ = 1 := by
    simpa [norm_coordinateEmbedding] using hb
  simpa [interblockRankOne] using
    (rankOne_apply_smul_source (coordinateEmbedding i a)
      (coordinateEmbedding j b) hnorm (1 : ℂ))

/-- An inter-block link vanishes on every coordinate distinct from its source
coordinate. -/
theorem interblockRankOne_apply_other (i j k : I) (hkj : k ≠ j)
    (a : H i) (b : H j) (x : H k) :
    interblockRankOne i j a b (coordinateEmbedding k x) = 0 := by
  apply rankOne_apply_eq_zero_of_inner_eq_zero
  exact inner_coordinateEmbedding_eq_zero hkj.symm b x

end MathlibAnnex.Analysis.InnerProductSpace
