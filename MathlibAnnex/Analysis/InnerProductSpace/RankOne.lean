import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Rank-one links for selected cyclic copies. These facts are deliberately about
the chosen vectors only; they make no ambient rank-one assertion for an
irreducible representation.
-/

set_option autoImplicit false

namespace MathlibAnnex.Analysis.InnerProductSpace

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A rank-one link kills every vector orthogonal to its source vector. -/
theorem rankOne_apply_eq_zero_of_inner_eq_zero (a b z : H)
    (hz : inner ℂ b z = 0) :
    InnerProductSpace.rankOne ℂ a b z = 0 := by
  simp [InnerProductSpace.rankOne_apply, hz]

/-- A rank-one link sends scalar multiples of its unit source vector as expected. -/
theorem rankOne_apply_smul_source (a b : H) (hb : ‖b‖ = 1) (c : ℂ) :
    InnerProductSpace.rankOne ℂ a b (c • b) = c • a := by
  simp [InnerProductSpace.rankOne_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hb]

/--
For pairwise orthogonal selected copies, the link sourced at copy `i` vanishes
on every distinct copy `j`. No statement about the whole ambient Hilbert space
is made.
-/
theorem rankOne_link_vanishes_on_other_copy {J K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (V : J → K →L[ℂ] H)
    (horth : ∀ i j : J, i ≠ j → ∀ x y : K, inner ℂ (V i x) (V j y) = 0)
    (o i j : J) (hji : j ≠ i) (xi eta : K) :
    InnerProductSpace.rankOne ℂ (V o xi) (V i xi) (V j eta) = 0 := by
  apply rankOne_apply_eq_zero_of_inner_eq_zero
  exact horth i j hji.symm xi eta

/-- The rank-one operator associated to a unit vector is an orthogonal
projection. -/
theorem isStarProjection_rankOne_self (x : H) (hx : ‖x‖ = 1) :
    IsStarProjection (InnerProductSpace.rankOne ℂ x x) := by
  constructor
  · rw [isIdempotentElem_iff]
    ext y
    simp [ContinuousLinearMap.mul_apply, InnerProductSpace.rankOne_apply,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne]

/-- The range of the unit-vector rank-one projection is its one-dimensional
span. -/
theorem range_rankOne_self (x : H) (hx : ‖x‖ = 1) :
    (InnerProductSpace.rankOne ℂ x x).range = ℂ ∙ x := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    exact Submodule.mem_span_singleton.mpr
      ⟨inner ℂ x z, InnerProductSpace.rankOne_apply _ _ _⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c • x, rankOne_apply_smul_source x x hx c⟩

/-- Orthogonal projection onto the span of a unit vector, in rank-one form. -/
theorem starProjection_span_singleton (x : H) (hx : ‖x‖ = 1) :
    letI : (ℂ ∙ x).HasOrthogonalProjection := inferInstance
    (ℂ ∙ x).starProjection = InnerProductSpace.rankOne ℂ x x := by
  letI : (ℂ ∙ x).HasOrthogonalProjection := inferInstance
  apply ContinuousLinearMap.ext
  intro y
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_span_singleton.mpr
      ⟨inner ℂ x y, InnerProductSpace.rankOne_apply x x y⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [InnerProductSpace.rankOne_apply, inner_sub_left,
      inner_smul_right, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx, inner_conj_symm y x]
    norm_num
    ring

/-- A submodule proved equal to the span of a unit vector has the expected
rank-one orthogonal projection, independently of how its projection instance
was obtained. -/
theorem starProjection_eq_rankOne_of_eq_span (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (x : H) (hx : ‖x‖ = 1)
    (hK : K = ℂ ∙ x) :
    K.starProjection = InnerProductSpace.rankOne ℂ x x := by
  apply ContinuousLinearMap.ext
  intro y
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hK]
    exact Submodule.mem_span_singleton.mpr
      ⟨inner ℂ x y, InnerProductSpace.rankOne_apply x x y⟩
  · intro z hz
    rw [hK] at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [InnerProductSpace.rankOne_apply, inner_sub_left,
      inner_smul_right, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx, inner_conj_symm y x]
    norm_num
    ring

/-- A common eigenvector for an operator and its adjoint determines a
rank-one projection commuting with that operator. -/
theorem commute_rankOne_self_of_apply_eq_smul_of_adjoint_apply_eq_star_smul
    (T : H →L[ℂ] H) (x : H) (c : ℂ)
    (hT : T x = c • x)
    (hTadj : ContinuousLinearMap.adjoint T x = star c • x) :
    T * InnerProductSpace.rankOne ℂ x x =
      InnerProductSpace.rankOne ℂ x x * T := by
  change T.comp (InnerProductSpace.rankOne ℂ x x) =
    (InnerProductSpace.rankOne ℂ x x).comp T
  rw [InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp,
    hT, hTadj]
  ext y
  simp [InnerProductSpace.rankOne_apply]

/--
The complete algebraic package for a link between two orthonormal selected
vectors: action, vanishing, adjoint, and both support products.
-/
theorem rankOne_link_relations (a b : H)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℂ a b = 0) :
    InnerProductSpace.rankOne ℂ a b b = a ∧
    InnerProductSpace.rankOne ℂ a b a = 0 ∧
    star (InnerProductSpace.rankOne ℂ a b) = InnerProductSpace.rankOne ℂ b a ∧
    star (InnerProductSpace.rankOne ℂ a b) * InnerProductSpace.rankOne ℂ a b =
      InnerProductSpace.rankOne ℂ b b ∧
    InnerProductSpace.rankOne ℂ a b * star (InnerProductSpace.rankOne ℂ a b) =
      InnerProductSpace.rankOne ℂ a a := by
  have haa : inner ℂ a a = 1 := by
    rw [inner_self_eq_norm_sq_to_K, ha]
    norm_num
  have hbb : inner ℂ b b = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hb]
    norm_num
  have hba : inner ℂ b a = 0 := by
    calc
      inner ℂ b a = star (inner ℂ a b) := (inner_conj_symm b a).symm
      _ = 0 := by simp [hab]
  constructor
  · simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hb]
  constructor
  · simp [InnerProductSpace.rankOne_apply, hba]
  constructor
  · simpa [ContinuousLinearMap.star_eq_adjoint] using
      (InnerProductSpace.adjoint_rankOne a b)
  constructor
  · ext z
    simp [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.rankOne_apply,
      InnerProductSpace.adjoint_rankOne, ha]
  · ext z
    simp [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.rankOne_apply,
      InnerProductSpace.adjoint_rankOne, hb]

end MathlibAnnex.Analysis.InnerProductSpace
