import MathlibAnnex.Analysis.CStarAlgebra.InvariantExponential
import MathlibAnnex.Analysis.CStarAlgebra.CAR.FiniteAverage
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-!
# Unitary lift from a finite CAR corner

This is the algebraic finite-corner part of the local transport construction.
It is stated inside the completed CAR algebra and uses the actual stage matrix
units.  No representation or homogeneity statement is assumed.
-/

set_option autoImplicit false

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace
open scoped Real

namespace MathlibAnnex.CStarAlgebra.CAR

/-- A unitary in the `e₀₀` corner, with the corner projection as its unit. -/
def IsRootCornerUnitary (n : ℕ) (z : Limit) : Prop :=
  let e := limitMatrixUnit n 0 0
  star z * z = e ∧ z * star z = e ∧ e * z = z ∧ z * e = z

theorem isStarProjection_limitMatrixUnit_zero_zero (n : ℕ) :
    IsStarProjection (limitMatrixUnit n 0 0) := by
  constructor
  · rw [isIdempotentElem_iff]
    simp
  · rw [isSelfAdjoint_iff]
    simp

/-- Matrix amplification of an element in the root corner. -/
noncomputable def cornerLift (n : ℕ) (z : Limit) : Limit :=
  ∑ i : Fin (2 ^ n),
    limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i

theorem cornerLift_eq_rowAverageLinear (n : ℕ) (z : Limit) :
    cornerLift n z = rowAverageLinear n z := rfl

@[simp]
theorem cornerLift_zero (n : ℕ) : cornerLift n 0 = 0 := by
  simp [cornerLift]

theorem star_cornerLift (n : ℕ) (z : Limit) :
    star (cornerLift n z) = cornerLift n (star z) := by
  classical
  simp only [cornerLift, star_sum, star_mul, star_limitMatrixUnit]
  apply Finset.sum_congr rfl
  intro i _
  noncomm_ring

private theorem cornerLift_mul_term (n : ℕ) (z : Limit)
    (hz : IsRootCornerUnitary n z) (i j : Fin (2 ^ n)) :
    (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) *
        (limitMatrixUnit n j 0 * star z * limitMatrixUnit n 0 j) =
      if i = j then limitMatrixUnit n i i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    calc
      (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) *
          (limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 i) =
          limitMatrixUnit n i 0 * z *
            (limitMatrixUnit n 0 i * limitMatrixUnit n i 0) *
              star z * limitMatrixUnit n 0 i := by noncomm_ring
      _ = limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 0 *
              star z * limitMatrixUnit n 0 i := by simp
      _ = limitMatrixUnit n i 0 * (z * limitMatrixUnit n 0 0) *
              star z * limitMatrixUnit n 0 i := by noncomm_ring
      _ = limitMatrixUnit n i 0 * (z * star z) *
              limitMatrixUnit n 0 i := by rw [hz.2.2.2]; noncomm_ring
      _ = limitMatrixUnit n i 0 * limitMatrixUnit n 0 0 *
              limitMatrixUnit n 0 i := by rw [hz.2.1]
      _ = limitMatrixUnit n i i := by simp
  · rw [if_neg hij]
    calc
      (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) *
          (limitMatrixUnit n j 0 * star z * limitMatrixUnit n 0 j) =
          limitMatrixUnit n i 0 * z *
            (limitMatrixUnit n 0 i * limitMatrixUnit n j 0) *
              star z * limitMatrixUnit n 0 j := by noncomm_ring
      _ = 0 := by rw [limitMatrixUnit_mul]; simp [hij]

private theorem cornerLift_star_mul_term (n : ℕ) (z : Limit)
    (hz : IsRootCornerUnitary n z) (i j : Fin (2 ^ n)) :
    (limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 i) *
        (limitMatrixUnit n j 0 * z * limitMatrixUnit n 0 j) =
      if i = j then limitMatrixUnit n i i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    calc
      (limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 i) *
          (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) =
          limitMatrixUnit n i 0 * star z *
            (limitMatrixUnit n 0 i * limitMatrixUnit n i 0) *
              z * limitMatrixUnit n 0 i := by noncomm_ring
      _ = limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 0 *
              z * limitMatrixUnit n 0 i := by simp
      _ = limitMatrixUnit n i 0 * star z *
              (limitMatrixUnit n 0 0 * z) * limitMatrixUnit n 0 i := by
                noncomm_ring
      _ = limitMatrixUnit n i 0 * (star z * z) *
              limitMatrixUnit n 0 i := by rw [hz.2.2.1]; noncomm_ring
      _ = limitMatrixUnit n i 0 * limitMatrixUnit n 0 0 *
              limitMatrixUnit n 0 i := by rw [hz.1]
      _ = limitMatrixUnit n i i := by simp
  · rw [if_neg hij]
    calc
      (limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 i) *
          (limitMatrixUnit n j 0 * z * limitMatrixUnit n 0 j) =
          limitMatrixUnit n i 0 * star z *
            (limitMatrixUnit n 0 i * limitMatrixUnit n j 0) *
              z * limitMatrixUnit n 0 j := by noncomm_ring
      _ = 0 := by rw [limitMatrixUnit_mul]; simp [hij]

set_option maxHeartbeats 800000 in
/-- A corner unitary amplifies to a unitary of the completed CAR algebra. -/
theorem cornerLift_mem_unitary (n : ℕ) (z : Limit)
    (hz : IsRootCornerUnitary n z) : cornerLift n z ∈ unitary Limit := by
  classical
  rw [Unitary.mem_iff, star_cornerLift]
  constructor
  · simp only [cornerLift, Finset.sum_mul, Finset.mul_sum]
    calc
      ∑ j, ∑ i,
          (limitMatrixUnit n i 0 * star z * limitMatrixUnit n 0 i) *
            (limitMatrixUnit n j 0 * z * limitMatrixUnit n 0 j) =
          ∑ j, ∑ i, if i = j then limitMatrixUnit n i i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact cornerLift_star_mul_term n z hz j i
      _ = 1 := by simp [sum_limitMatrixUnit_diag]
  · simp only [cornerLift, Finset.sum_mul, Finset.mul_sum]
    calc
      ∑ j, ∑ i,
          (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) *
            (limitMatrixUnit n j 0 * star z * limitMatrixUnit n 0 j) =
          ∑ j, ∑ i, if i = j then limitMatrixUnit n i i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact cornerLift_mul_term n z hz j i
      _ = 1 := by simp [sum_limitMatrixUnit_diag]

private theorem cornerLift_mul_matrixUnit (n : ℕ) (z : Limit)
    (p q : Fin (2 ^ n)) :
    cornerLift n z * limitMatrixUnit n p q =
      limitMatrixUnit n p 0 * z * limitMatrixUnit n 0 q := by
  classical
  simp only [cornerLift, Finset.sum_mul]
  rw [Finset.sum_eq_single p]
  · calc
      (limitMatrixUnit n p 0 * z * limitMatrixUnit n 0 p) *
          limitMatrixUnit n p q =
          limitMatrixUnit n p 0 * z *
            (limitMatrixUnit n 0 p * limitMatrixUnit n p q) := by
              noncomm_ring
      _ = _ := by simp
  · intro i _ hip
    calc
      (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) *
          limitMatrixUnit n p q =
          limitMatrixUnit n i 0 * z *
            (limitMatrixUnit n 0 i * limitMatrixUnit n p q) := by
              noncomm_ring
      _ = 0 := by rw [limitMatrixUnit_mul]; simp [hip]
  · simp

private theorem matrixUnit_mul_cornerLift (n : ℕ) (z : Limit)
    (p q : Fin (2 ^ n)) :
    limitMatrixUnit n p q * cornerLift n z =
      limitMatrixUnit n p 0 * z * limitMatrixUnit n 0 q := by
  classical
  simp only [cornerLift, Finset.mul_sum]
  rw [Finset.sum_eq_single q]
  · calc
      limitMatrixUnit n p q *
          (limitMatrixUnit n q 0 * z * limitMatrixUnit n 0 q) =
          (limitMatrixUnit n p q * limitMatrixUnit n q 0) * z *
            limitMatrixUnit n 0 q := by noncomm_ring
      _ = _ := by simp
  · intro i _ hiq
    calc
      limitMatrixUnit n p q *
          (limitMatrixUnit n i 0 * z * limitMatrixUnit n 0 i) =
          (limitMatrixUnit n p q * limitMatrixUnit n i 0) * z *
            limitMatrixUnit n 0 i := by noncomm_ring
      _ = 0 := by rw [limitMatrixUnit_mul]; simp [Ne.symm hiq]
  · simp

/-- The amplified corner unitary commutes exactly with every matrix unit in
the chosen finite stage. -/
theorem cornerLift_commute_matrixUnit (n : ℕ) (z : Limit)
    (p q : Fin (2 ^ n)) :
    Commute (cornerLift n z) (limitMatrixUnit n p q) := by
  rw [Commute, SemiconjBy,
    cornerLift_mul_matrixUnit n z p q,
    matrixUnit_mul_cornerLift n z p q]

/-- The lift centralizes the whole chosen finite matrix stage, not merely its
displayed matrix units. -/
theorem ofStage_commute_cornerLift (n : ℕ) (c : Stage n) (z : Limit) :
    Commute (ofStage n c) (cornerLift n z) := by
  rw [cornerLift_eq_rowAverageLinear]
  exact ofStage_commute_rowAverage n c z

/-- The exponential of a supported self-adjoint corner element, with the
corner projection inserted as the corner unit. -/
noncomputable def cornerExponential (n : ℕ) (h : selfAdjoint Limit) : Limit :=
  limitMatrixUnit n 0 0 * (selfAdjoint.expUnitary h : Limit)

/-- A supported self-adjoint element exponentiates to a genuine unitary in
the root corner. -/
theorem isRootCornerUnitary_cornerExponential (n : ℕ)
    (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h) :
    IsRootCornerUnitary n (cornerExponential n h) := by
  let e : Limit := limitMatrixUnit n 0 0
  let u : Limit := selfAdjoint.expUnitary h
  have heidem : e * e = e := by simp [e]
  have hestar : star e = e := by simp [e]
  have heu : Commute e u := by
    have hehcomm : Commute e (h : Limit) := by
      rw [Commute, SemiconjBy]
      exact heh.trans hhe.symm
    dsimp [u]
    exact (hehcomm.smul_right Complex.I).exp_right
  have hu : u ∈ unitary Limit := (selfAdjoint.expUnitary h).property
  change star (e * u) * (e * u) = e ∧
    (e * u) * star (e * u) = e ∧ e * (e * u) = e * u ∧
      (e * u) * e = e * u
  constructor
  · calc
      star (e * u) * (e * u) = star u * e * (e * u) := by rw [star_mul, hestar]
      _ = star u * ((e * e) * u) := by noncomm_ring
      _ = star u * (e * u) := by rw [heidem]
      _ = star u * (u * e) := by rw [heu.eq]
      _ = (star u * u) * e := by rw [mul_assoc]
      _ = e := by rw [hu.1, one_mul]
  constructor
  · calc
      (e * u) * star (e * u) = e * u * (star u * e) := by rw [star_mul, hestar]
      _ = e * (u * star u) * e := by noncomm_ring
      _ = e := by rw [hu.2, mul_one, heidem]
  constructor
  · rw [← mul_assoc, heidem]
  · calc
      (e * u) * e = e * (u * e) := by rw [mul_assoc]
      _ = e * (e * u) := by rw [heu.eq]
      _ = e * u := by rw [← mul_assoc, heidem]

/-- The fully amplified corner exponential as an ambient CAR unitary. -/
noncomputable def liftedCornerExponential (n : ℕ) (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h) : unitary Limit :=
  ⟨cornerLift n (cornerExponential n h),
    cornerLift_mem_unitary n (cornerExponential n h)
      (isRootCornerUnitary_cornerExponential n h heh hhe)⟩

/-- The canonical path from the ambient unit to a lifted corner exponential.
Every intermediate generator remains supported in the same root corner. -/
noncomputable def liftedCornerExponentialPath (n : ℕ) (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h) :
    Path 1 (liftedCornerExponential n h heh hhe) where
  toFun t := liftedCornerExponential n ((t : ℝ) • h)
    (by
      change limitMatrixUnit n 0 0 * ((t : ℝ) • (h : Limit)) =
        (t : ℝ) • (h : Limit)
      rw [mul_smul_comm, heh])
    (by
      change ((t : ℝ) • (h : Limit)) * limitMatrixUnit n 0 0 =
        (t : ℝ) • (h : Limit)
      rw [smul_mul_assoc, hhe])
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
      rowAverage n (limitMatrixUnit n 0 0 *
        (selfAdjoint.expUnitary ((t : ℝ) • h) : Limit)))
    have hsmul : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (t : ℝ) • h) := by
      apply continuous_induced_rng.mpr
      change Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
        ((t : ℝ) : ℂ) • (h : Limit))
      fun_prop
    have hexp : Continuous (fun t : Set.Icc (0 : ℝ) 1 =>
        (selfAdjoint.expUnitary ((t : ℝ) • h) : Limit)) :=
      continuous_subtype_val.comp
        (selfAdjoint.continuous_expUnitary.comp hsmul)
    exact (rowAverage n).continuous.comp (continuous_const.mul hexp)
  source' := by
    apply Subtype.ext
    simp [liftedCornerExponential, cornerExponential, cornerLift,
      sum_limitMatrixUnit_diag]
  target' := by
    apply Subtype.ext
    have hone : ((1 : ℝ) • h : selfAdjoint Limit) = h := by
      apply Subtype.ext
      change ((1 : ℝ) : ℂ) • (h : Limit) = (h : Limit)
      simp
    change cornerLift n (cornerExponential n ((1 : ℝ) • h)) =
      cornerLift n (cornerExponential n h)
    rw [hone]

/-- Representation formula for the lifted corner action. -/
theorem representation_cornerLift_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Representation Limit H) (n : ℕ) (z : Limit) (ξ : H) :
    ρ (cornerLift n z) ξ =
      ∑ i : Fin (2 ^ n),
        ρ (limitMatrixUnit n i 0)
          (ρ z (ρ (limitMatrixUnit n 0 i) ξ)) := by
  simp [cornerLift, map_sum, map_mul]

/-- Every lifted corner exponential centralizes its source stage exactly. -/
theorem liftedCornerExponential_commute_stage (n : ℕ) (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h) (c : Stage n) :
    Commute (ofStage n c) (liftedCornerExponential n h heh hhe : Limit) :=
  ofStage_commute_cornerLift n c (cornerExponential n h)

/-- The lifted exponential centralizes the source stage at every time along
its canonical path, not only at the endpoint. -/
theorem liftedCornerExponentialPath_commute_stage (n : ℕ)
    (h : selfAdjoint Limit)
    (heh : limitMatrixUnit n 0 0 * (h : Limit) = h)
    (hhe : (h : Limit) * limitMatrixUnit n 0 0 = h)
    (t : Set.Icc (0 : ℝ) 1) (c : Stage n) :
    Commute (ofStage n c) (liftedCornerExponentialPath n h heh hhe t : Limit) := by
  exact liftedCornerExponential_commute_stage n ((t : ℝ) • h)
    (by
      change limitMatrixUnit n 0 0 * ((t : ℝ) • (h : Limit)) =
        (t : ℝ) • (h : Limit)
      rw [mul_smul_comm, heh])
    (by
      change ((t : ℝ) • (h : Limit)) * limitMatrixUnit n 0 0 =
        (t : ℝ) • (h : Limit)
      rw [smul_mul_assoc, hhe]) c

/-- The pointwise product of two lifted corner-exponential paths. -/
noncomputable def liftedCornerExponentialPairPath (n : ℕ)
    (h₁ h₂ : selfAdjoint Limit)
    (heh₁ : limitMatrixUnit n 0 0 * (h₁ : Limit) = h₁)
    (hh₁e : (h₁ : Limit) * limitMatrixUnit n 0 0 = h₁)
    (heh₂ : limitMatrixUnit n 0 0 * (h₂ : Limit) = h₂)
    (hh₂e : (h₂ : Limit) * limitMatrixUnit n 0 0 = h₂) :
    Path 1
      (liftedCornerExponential n h₂ heh₂ hh₂e *
        liftedCornerExponential n h₁ heh₁ hh₁e) where
  toFun t := liftedCornerExponentialPath n h₂ heh₂ hh₂e t *
    liftedCornerExponentialPath n h₁ heh₁ hh₁e t
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    exact congrArg₂ (· * ·)
      (liftedCornerExponentialPath n h₂ heh₂ hh₂e).target
      (liftedCornerExponentialPath n h₁ heh₁ hh₁e).target

/-- Both factors of the paired path centralize the source stage at every
time, hence so does their product. -/
theorem liftedCornerExponentialPairPath_commute_stage (n : ℕ)
    (h₁ h₂ : selfAdjoint Limit)
    (heh₁ : limitMatrixUnit n 0 0 * (h₁ : Limit) = h₁)
    (hh₁e : (h₁ : Limit) * limitMatrixUnit n 0 0 = h₁)
    (heh₂ : limitMatrixUnit n 0 0 * (h₂ : Limit) = h₂)
    (hh₂e : (h₂ : Limit) * limitMatrixUnit n 0 0 = h₂)
    (t : Set.Icc (0 : ℝ) 1) (c : Stage n) :
    Commute (ofStage n c)
      (liftedCornerExponentialPairPath n h₁ h₂ heh₁ hh₁e heh₂ hh₂e t : Limit) :=
  (liftedCornerExponentialPath_commute_stage n h₂ heh₂ hh₂e t c).mul_right
    (liftedCornerExponentialPath_commute_stage n h₁ heh₁ hh₁e t c)

/-- CAR specialization of the supported quantitative Kadison theorem.  The
witness is already a self-adjoint element of the actual finite-stage root
corner, ready for corner exponentiation and amplification. -/
theorem exists_rootCornerSupported_selfAdjoint_norm_le_one_apply_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (ρ : Representation Limit H) (hρ : StarAlgHom.IsIrreducible ρ)
    (n : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
    (ξ : I → H) (hξ : ∀ i, ρ (limitMatrixUnit n 0 0) (ξ i) = ξ i)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (hTnorm : ‖T‖ ≤ 1)
    (hTrange : ρ (limitMatrixUnit n 0 0) * T = T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : selfAdjoint Limit, ‖(h : Limit)‖ ≤ 1 ∧
      limitMatrixUnit n 0 0 * (h : Limit) = h ∧
      (h : Limit) * limitMatrixUnit n 0 0 = h ∧
      ‖atomicRepresentation (fun _ : I => ρ) (h : Limit) (finiteHilbertSum ξ) -
        diagonal (fun _ : I => T) ‖T‖ (norm_nonneg T) (fun _ => le_rfl)
          (finiteHilbertSum ξ)‖ < ε := by
  obtain ⟨a, ha, hanorm, haleft, haright, happ⟩ :=
    ρ.exists_cornerSupported_selfAdjoint_norm_le_one_atomic_apply_sub_norm_lt
      hρ (isStarProjection_limitMatrixUnit_zero_zero n) ξ hξ T hT hTnorm
        hTrange hε
  exact ⟨⟨a, ha⟩, hanorm, haleft, haright, happ⟩

/-- Exact, coarse-norm CAR corner interpolation on a finite-dimensional active
subspace.  This is the exact counterpart of the one-shot approximation above. -/
theorem exists_rootCornerSupported_selfAdjoint_norm_le_two_mul_and_eq_on
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → rho (limitMatrixUnit n 0 0) x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTrange : rho (limitMatrixUnit n 0 0) * T = T) :
    ∃ h : selfAdjoint Limit, ‖(h : Limit)‖ ≤ 2 * ‖T‖ ∧
      limitMatrixUnit n 0 0 * (h : Limit) = h ∧
      (h : Limit) * limitMatrixUnit n 0 0 = h ∧
      ∀ x : H, x ∈ E → rho (h : Limit) x = T x := by
  obtain ⟨a, ha, hanorm, haleft, haright, hexact⟩ :=
    rho.exists_cornerSupported_selfAdjoint_norm_le_two_mul_and_eq_on
      hrho (isStarProjection_limitMatrixUnit_zero_zero n) E hE T hT hTrange
  exact ⟨⟨a, ha⟩, hanorm, haleft, haright, hexact⟩

/-- A finite-dimensional invariant self-adjoint operator can be lifted into the
root CAR corner so that the corresponding corner exponential has exactly the
prescribed exponential action on the active subspace. -/
theorem exists_rootCornerSupported_exponential_eq_on
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    [FiniteDimensional ℂ E]
    (hE : ∀ x : H, x ∈ E → rho (limitMatrixUnit n 0 0) x = x)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hTrange : rho (limitMatrixUnit n 0 0) * T = T)
    (hTmap : Set.MapsTo T E E) :
    ∃ h : selfAdjoint Limit, ‖(h : Limit)‖ ≤ 2 * ‖T‖ ∧
      limitMatrixUnit n 0 0 * (h : Limit) = h ∧
      (h : Limit) * limitMatrixUnit n 0 0 = h ∧
      ∀ x : H, x ∈ E →
        rho (cornerExponential n h) x =
          NormedSpace.exp (Complex.I • T) x := by
  obtain ⟨h, hnorm, heh, hhe, hexact⟩ :=
    exists_rootCornerSupported_selfAdjoint_norm_le_two_mul_and_eq_on
      rho hrho n E hE T hT hTrange
  refine ⟨h, hnorm, heh, hhe, fun x hx => ?_⟩
  have hehcomm : Commute (limitMatrixUnit n 0 0) (h : Limit) := by
    rw [Commute, SemiconjBy]
    exact heh.trans hhe.symm
  have heexp : Commute (limitMatrixUnit n 0 0)
      (selfAdjoint.expUnitary h : Limit) := by
    simpa only [selfAdjoint.expUnitary_coe] using
      (hehcomm.smul_right Complex.I).exp_right
  calc
    rho (cornerExponential n h) x =
        rho (limitMatrixUnit n 0 0)
          (rho (selfAdjoint.expUnitary h : Limit) x) := by
      simp [cornerExponential, map_mul]
    _ = rho (selfAdjoint.expUnitary h : Limit)
          (rho (limitMatrixUnit n 0 0) x) := by
      exact congrArg (fun S : H →L[ℂ] H => S x) (heexp.map rho).eq
    _ = rho (selfAdjoint.expUnitary h : Limit) x := by rw [hE x hx]
    _ = NormedSpace.exp (Complex.I • T) x :=
      rho.expUnitary_apply_eq_of_eqOn_of_mapsTo h T E hexact hTmap hx

end MathlibAnnex.CStarAlgebra.CAR
