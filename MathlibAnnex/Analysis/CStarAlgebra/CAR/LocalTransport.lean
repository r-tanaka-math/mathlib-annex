import MathlibAnnex.Analysis.CStarAlgebra.CAR.InvolutionLift
import MathlibAnnex.Analysis.InnerProductSpace.GramPerturbation
import MathlibAnnex.Analysis.InnerProductSpace.FiniteEmbedding

set_option autoImplicit false

noncomputable section

open MathlibAnnex.Analysis.CStarAlgebra
open MathlibAnnex.Analysis.InnerProductSpace
open MathlibAnnex.InnerProductSpace

namespace MathlibAnnex.CStarAlgebra.CAR

set_option maxHeartbeats 1000000 in
theorem exists_delta_liftedCornerUnitary_path_apply_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n d : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta > 0,
      ∀ (v w : Fin d → rootCornerSubspace rho n),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < delta) →
        ∃ u : unitary Limit,
          (∀ c : Stage n, Commute (ofStage n c) (u : Limit)) ∧
          (∃ p : Path 1 u, ∀ t c,
            Commute (ofStage n c) (p t : Limit)) ∧
          ∀ i, ‖rho (u : Limit) (v i : H) - (w i : H)‖ < tau := by
  obtain ⟨delta, hdelta, hperturb⟩ :=
    exists_delta_orthogonalGramPerturbation (n := d) (half_pos htau)
  refine ⟨delta, hdelta, ?_⟩
  intro v w hv hw hgram
  let e : Limit := limitMatrixUnit n 0 0
  let K : Submodule ℂ H := rootCornerSubspace rho n
  have hroot : IsStarProjection (rho e) :=
    (isStarProjection_limitMatrixUnit_zero_zero n).map rho
  letI : CompleteSpace K := IsComplete.completeSpace_coe
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      hroot.isIdempotentElem).isComplete
  have hKnot : ¬ FiniteDimensional ℂ K := by
    simpa [K, e, rootCornerSubspace] using
      not_finiteDimensional_range_rootCorner rho
        ((Representation.isIrreducible_iff_starAlgHom rho).mpr hrho) n
  let V : Submodule ℂ K :=
    Submodule.span ℂ (Set.range v ∪ Set.range w)
  letI : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ
      ((Set.finite_range v).union (Set.finite_range w))
  letI : V.HasOrthogonalProjection := inferInstance
  let R : Submodule ℂ K := Vᗮ
  letI : CompleteSpace R := IsComplete.completeSpace_coe
    (show IsClosed (R : Set K) by
      simpa [R] using Submodule.isClosed_orthogonal V).isComplete
  have hRnot : ¬ FiniteDimensional ℂ R := by
    intro hR
    letI : FiniteDimensional ℂ R := hR
    have htop : V ⊔ R = ⊤ := by
      simpa [R] using
        (Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := V))
    letI : FiniteDimensional ℂ (V ⊔ R : Submodule ℂ K) := inferInstance
    apply hKnot
    exact FiniteDimensional.of_surjective (V ⊔ R).subtype (fun x =>
      ⟨⟨x, by rw [htop]; simp⟩, rfl⟩)
  let S : Submodule ℂ K := Submodule.span ℂ (Set.range v)
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  obtain ⟨L⟩ :=
    nonempty_linearIsometry_of_finiteDimensional_of_not_finiteDimensional
      (E := S) (F := R) hRnot
  let vS : Fin d → S := fun i =>
    ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  let z : Fin d → K := fun i => (L (vS i) : R)
  have hvV (i : Fin d) : v i ∈ V :=
    Submodule.subset_span (Or.inl (Set.mem_range_self i))
  have hwV (i : Fin d) : w i ∈ V :=
    Submodule.subset_span (Or.inr (Set.mem_range_self i))
  have hzR (i : Fin d) : z i ∈ R := (L (vS i)).property
  have hzgram (i j : Fin d) :
      inner ℂ (z i) (z j) = inner ℂ (v i) (v j) := by
    change inner ℂ (L (vS i)) (L (vS j)) = inner ℂ (vS i) (vS j)
    exact L.inner_map_map (vS i) (vS j)
  have hzsum : (∑ i, ‖z i‖ ^ 2) ≤ 1 := by
    calc
      (∑ i, ‖z i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show ‖z i‖ = ‖v i‖ by exact L.norm_map (vS i)]
      _ ≤ 1 := hv
  have hvzorth : ∀ i j, inner ℂ (v i) (z j) = 0 := by
    intro i j
    exact V.inner_right_of_mem_orthogonal (hvV i) (hzR j)
  have hzworth : ∀ i j, inner ℂ (z i) (w j) = 0 := by
    intro i j
    exact V.inner_left_of_mem_orthogonal (hwV j) (hzR i)
  obtain ⟨U1, hU1, -, hU1sq, hU1finite⟩ :=
    hperturb v z hv hzsum hvzorth (by
      intro i j
      rw [hzgram]
      simpa using hdelta)
  obtain ⟨U2, hU2, -, hU2sq, hU2finite⟩ :=
    hperturb z w hzsum hw hzworth (by
      intro i j
      rw [hzgram]
      exact hgram i j)
  letI : FiniteDimensional ℂ
      (LinearMap.range (U1.toLinearMap - LinearMap.id)) := hU1finite
  obtain ⟨h1, heh1, hhe1, hu1exact⟩ :=
    exists_liftedCornerExponential_apply_eq_involution
      rho hrho n d v U1 hU1sq
  letI : FiniteDimensional ℂ
      (LinearMap.range (U2.toLinearMap - LinearMap.id)) := hU2finite
  obtain ⟨h2, heh2, hhe2, hu2exact⟩ :=
    exists_liftedCornerExponential_apply_eq_involution
      rho hrho n d z U2 hU2sq
  let u1 : unitary Limit := liftedCornerExponential n h1 heh1 hhe1
  let u2 : unitary Limit := liftedCornerExponential n h2 heh2 hhe2
  let u : unitary Limit := u2 * u1
  refine ⟨u, ?_, ?_, ?_⟩
  · intro c
    exact (liftedCornerExponential_commute_stage n h2 heh2 hhe2 c).mul_right
      (liftedCornerExponential_commute_stage n h1 heh1 hhe1 c)
  · refine ⟨liftedCornerExponentialPairPath n h1 h2 heh1 hhe1 heh2 hhe2, ?_⟩
    intro t c
    exact liftedCornerExponentialPairPath_commute_stage
      n h1 h2 heh1 hhe1 heh2 hhe2 t c
  · intro i
    have hu2unit : rho (u2 : Limit) ∈ unitary (H →L[ℂ] H) :=
      Unitary.map_mem rho u2.property
    change ‖rho ((u2 : Limit) * (u1 : Limit)) (v i : H) - (w i : H)‖ < tau
    rw [map_mul, mul_apply_eq_comp, hu1exact i]
    have hdecomp :
        rho (u2 : Limit) (U1 (v i) : H) - (w i : H) =
          rho (u2 : Limit) ((U1 (v i) : H) - (z i : H)) +
            (rho (u2 : Limit) (z i : H) - (w i : H)) := by
      rw [map_sub]
      module
    rw [hdecomp]
    calc
      _ ≤ ‖rho (u2 : Limit) ((U1 (v i) : H) - (z i : H))‖ +
          ‖rho (u2 : Limit) (z i : H) - (w i : H)‖ := norm_add_le _ _
      _ = ‖(U1 (v i) : H) - (z i : H)‖ +
          ‖(U2 (z i) : H) - (w i : H)‖ := by
        rw [(rho (u2 : Limit)).norm_map_of_mem_unitary hu2unit,
          hu2exact i]
      _ < tau / 2 + tau / 2 := add_lt_add (hU1 i) (hU2 i)
      _ = tau := by ring

set_option maxHeartbeats 1000000 in
/-- Compatibility form of finite-corner local transport, retaining the
endpoint statement while the stronger theorem also returns its canonical
all-time stage-central path. -/
theorem exists_delta_liftedCornerUnitary_apply_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n d : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta > 0,
      ∀ (v w : Fin d → rootCornerSubspace rho n),
        (∑ i, ‖v i‖ ^ 2) ≤ 1 → (∑ i, ‖w i‖ ^ 2) ≤ 1 →
        (∀ i j, ‖inner ℂ (v i) (v j) - inner ℂ (w i) (w j)‖ < delta) →
        ∃ u : unitary Limit,
          (∀ c : Stage n, Commute (ofStage n c) (u : Limit)) ∧
          ∀ i, ‖rho (u : Limit) (v i : H) - (w i : H)‖ < tau := by
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_liftedCornerUnitary_path_apply_sub_norm_lt
      rho hrho n d htau
  refine ⟨delta, hdelta, ?_⟩
  intro v w hv hw hgram
  obtain ⟨u, hcomm, -, hmove⟩ := hmain v w hv hw hgram
  exact ⟨u, hcomm, hmove⟩

set_option maxHeartbeats 800000 in
/-- Entrywise closeness of the two vector states on one full CAR stage gives
an ambient unitary which centralizes that stage and moves the first vector
close to the second.  The modulus is fixed before the vectors. -/
theorem exists_delta_stageCentral_unitary_path_apply_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        (∀ c : Stage n, Commute (ofStage n c) (u : Limit)) ∧
        (∃ p : Path 1 u, ∀ t c,
          Commute (ofStage n c) (p t : Limit)) ∧
        ‖rho (u : Limit) xi - eta‖ < tau := by
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_liftedCornerUnitary_path_apply_sub_norm_lt
      rho hrho n (2 ^ n) (div_pos htau (by positivity : (0 : ℝ) < 2 ^ n))
  refine ⟨delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  let v : Fin (2 ^ n) → rootCornerSubspace rho n := fun i =>
    ⟨rho (limitMatrixUnit n 0 i) xi, by
      refine ⟨rho (limitMatrixUnit n 0 i) xi, ?_⟩
      change (rho (limitMatrixUnit n 0 0) *
        rho (limitMatrixUnit n 0 i)) xi = _
      rw [← map_mul]
      simp⟩
  let w : Fin (2 ^ n) → rootCornerSubspace rho n := fun i =>
    ⟨rho (limitMatrixUnit n 0 i) eta, by
      refine ⟨rho (limitMatrixUnit n 0 i) eta, ?_⟩
      change (rho (limitMatrixUnit n 0 0) *
        rho (limitMatrixUnit n 0 i)) eta = _
      rw [← map_mul]
      simp⟩
  have hvsum : (∑ i, ‖v i‖ ^ 2) ≤ 1 := by
    have hv := sum_norm_sq_map_limitMatrixUnit_star rho n xi
    rw [hxi] at hv
    simpa [v] using hv.le
  have hwsum : (∑ i, ‖w i‖ ^ 2) ≤ 1 := by
    have hw := sum_norm_sq_map_limitMatrixUnit_star rho n eta
    rw [heta] at hw
    simpa [w] using hw.le
  obtain ⟨u, hcomm, hpath, hmove⟩ := hmain v w hvsum hwsum (by
    intro i j
    change ‖inner ℂ (rho (limitMatrixUnit n 0 i) xi)
      (rho (limitMatrixUnit n 0 j) xi) -
      inner ℂ (rho (limitMatrixUnit n 0 i) eta)
        (rho (limitMatrixUnit n 0 j) eta)‖ < delta
    rw [show inner ℂ (rho (limitMatrixUnit n 0 i) xi)
          (rho (limitMatrixUnit n 0 j) xi) =
        Representation.vectorFunctional rho xi (limitMatrixUnit n i j) by
      simpa using Representation.inner_map_star_apply rho xi
        (limitMatrixUnit n i 0) (limitMatrixUnit n j 0)]
    rw [show inner ℂ (rho (limitMatrixUnit n 0 i) eta)
          (rho (limitMatrixUnit n 0 j) eta) =
        Representation.vectorFunctional rho eta (limitMatrixUnit n i j) by
      simpa using Representation.inner_map_star_apply rho eta
        (limitMatrixUnit n i 0) (limitMatrixUnit n j 0)]
    exact hstate i j)
  refine ⟨u, hcomm, hpath, ?_⟩
  have hxiDecomp :
      xi = ∑ i : Fin (2 ^ n),
        rho (limitMatrixUnit n i 0) (v i : H) := by
    calc
      xi = rho 1 xi := by simp
      _ = rho (∑ i : Fin (2 ^ n), limitMatrixUnit n i i) xi := by
        rw [sum_limitMatrixUnit_diag]
      _ = ∑ i : Fin (2 ^ n), rho (limitMatrixUnit n i i) xi := by
        rw [map_sum]
        let ev : (H →L[ℂ] H) →+ H :=
          { toFun := fun T => T xi
            map_zero' := by simp
            map_add' := by intro S T; simp }
        exact map_sum ev _ _
      _ = ∑ i : Fin (2 ^ n),
          rho (limitMatrixUnit n i 0) (v i : H) := by
        apply Finset.sum_congr rfl
        intro i _
        change rho (limitMatrixUnit n i i) xi =
          rho (limitMatrixUnit n i 0) (rho (limitMatrixUnit n 0 i) xi)
        rw [← mul_apply_eq_comp, ← map_mul]
        simp
  have hetaDecomp :
      eta = ∑ i : Fin (2 ^ n),
        rho (limitMatrixUnit n i 0) (w i : H) := by
    calc
      eta = rho 1 eta := by simp
      _ = rho (∑ i : Fin (2 ^ n), limitMatrixUnit n i i) eta := by
        rw [sum_limitMatrixUnit_diag]
      _ = ∑ i : Fin (2 ^ n), rho (limitMatrixUnit n i i) eta := by
        rw [map_sum]
        let ev : (H →L[ℂ] H) →+ H :=
          { toFun := fun T => T eta
            map_zero' := by simp
            map_add' := by intro S T; simp }
        exact map_sum ev _ _
      _ = ∑ i : Fin (2 ^ n),
          rho (limitMatrixUnit n i 0) (w i : H) := by
        apply Finset.sum_congr rfl
        intro i _
        change rho (limitMatrixUnit n i i) eta =
          rho (limitMatrixUnit n i 0) (rho (limitMatrixUnit n 0 i) eta)
        rw [← mul_apply_eq_comp, ← map_mul]
        simp
  have haction :
      rho (u : Limit) xi - eta =
        ∑ i : Fin (2 ^ n), rho (limitMatrixUnit n i 0)
          (rho (u : Limit) (v i : H) - (w i : H)) := by
    rw [hxiDecomp, hetaDecomp, map_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sub]
    have hc := (hcomm (matrixUnit n i 0)).map rho
    have hcapp := congrArg (fun T : H →L[ℂ] H => T (v i : H)) hc.eq
    simpa [limitMatrixUnit, mul_apply_eq_comp] using hcapp.symm
  have hmatrixNorm (i : Fin (2 ^ n)) :
      ‖rho (limitMatrixUnit n i 0)‖ ≤ 1 := by
    have hsquare :
        ‖rho (limitMatrixUnit n i 0)‖ * ‖rho (limitMatrixUnit n i 0)‖ =
          ‖rho (limitMatrixUnit n 0 0)‖ := by
      rw [← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
      simp
    have hproj := IsStarProjection.norm_le (rho (limitMatrixUnit n 0 0))
      ((isStarProjection_limitMatrixUnit_zero_zero n).map rho)
    nlinarith [norm_nonneg (rho (limitMatrixUnit n i 0))]
  rw [haction]
  calc
    _ ≤ ∑ i : Fin (2 ^ n),
        ‖rho (limitMatrixUnit n i 0)
          (rho (u : Limit) (v i : H) - (w i : H))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (2 ^ n),
        ‖rho (u : Limit) (v i : H) - (w i : H)‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖rho (limitMatrixUnit n i 0)‖ *
            ‖rho (u : Limit) (v i : H) - (w i : H)‖ :=
          (rho (limitMatrixUnit n i 0)).le_opNorm _
        _ ≤ 1 * ‖rho (u : Limit) (v i : H) - (w i : H)‖ := by
          gcongr
          exact hmatrixNorm i
        _ = _ := one_mul _
    _ < ∑ _i : Fin (2 ^ n), tau / (2 ^ n : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro i _
      exact hmove i
    _ = tau := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      field_simp
      norm_cast

set_option maxHeartbeats 800000 in
/-- Compatibility endpoint for stage-central transport.  The strengthened
form above additionally retains an explicit path which is exactly
stage-central at every time. -/
theorem exists_delta_stageCentral_unitary_apply_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        (∀ c : Stage n, Commute (ofStage n c) (u : Limit)) ∧
        ‖rho (u : Limit) xi - eta‖ < tau := by
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_stageCentral_unitary_path_apply_sub_norm_lt
      rho hrho n htau
  refine ⟨delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  obtain ⟨u, hcomm, -, hmove⟩ := hmain xi eta hxi heta hstate
  exact ⟨u, hcomm, hmove⟩

set_option maxHeartbeats 800000 in
/-- Once a stage is fixed, entrywise closeness of two unit vector states on
that stage gives an exact vector transport.  The implementing unitary has a
commutator bound on the whole stage.  The exact correction is made after a
stage-central finite-corner transport, so its modulus is chosen before the
vectors. -/
theorem exists_delta_exact_unitary_path_apply_eq_and_stage_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        rho (u : Limit) xi = eta ∧
        ∃ p : Path 1 u, ∀ t c,
          ‖(p t : Limit) * ofStage n c - ofStage n c * (p t : Limit)‖ ≤
            epsilon * ‖ofStage n c‖ := by
  let epsilon0 : ℝ := min (epsilon / 2) 1
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    positivity
  obtain ⟨tau, htau, hsmall⟩ :=
    StarAlgHom.exists_unitary_apply_eq_and_norm_sub_one_lt
      rho hrho hepsilon0
  obtain ⟨delta, hdelta, hstage⟩ :=
    exists_delta_stageCentral_unitary_path_apply_sub_norm_lt rho hrho n htau
  refine ⟨delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  obtain ⟨u0, hcentral, ⟨p0, hp0⟩, hclose⟩ :=
    hstage xi eta hxi heta hstate
  have hu0map : rho (u0 : Limit) ∈ unitary (H →L[ℂ] H) :=
    Unitary.map_mem rho u0.property
  have hzeta : ‖rho (u0 : Limit) xi‖ = 1 := by
    rw [(rho (u0 : Limit)).norm_map_of_mem_unitary hu0map, hxi]
  obtain ⟨v, hvapply, hvnorm⟩ :=
    hsmall (rho (u0 : Limit) xi) eta hzeta heta hclose
  have hvhalf : ‖(v : Limit) - 1‖ < epsilon / 2 :=
    hvnorm.trans_le (min_le_left _ _)
  have hvTwo : ‖(v : Limit) - 1‖ < 2 := by
    calc
      _ < 1 := hvnorm.trans_le (min_le_right _ _)
      _ < 2 := by norm_num
  let pv : Path (1 : unitary Limit) v := Unitary.path 1 v (by
    simpa using hvTwo)
  let u : unitary Limit := v * u0
  let q : Path u0 u :=
    { toFun := fun t => pv t * u0
      continuous_toFun := by fun_prop
      source' := by rw [pv.source]; simp
      target' := by rw [pv.target] }
  let p : Path 1 u := p0.trans q
  refine ⟨u, ?_, p, ?_⟩
  · change rho ((v : Limit) * (u0 : Limit)) xi = eta
    rw [map_mul, mul_apply_eq_comp, hvapply]
  · have hp0bound (t : Set.Icc (0 : ℝ) 1) (c : Stage n) :
        ‖(p0 t : Limit) * ofStage n c -
            ofStage n c * (p0 t : Limit)‖ ≤
          epsilon * ‖ofStage n c‖ := by
      rw [(hp0 t c).eq]
      simp only [sub_self, norm_zero]
      positivity
    have hqbound (t : Set.Icc (0 : ℝ) 1) (c : Stage n) :
        ‖(q t : Limit) * ofStage n c -
            ofStage n c * (q t : Limit)‖ ≤
          epsilon * ‖ofStage n c‖ := by
      have hpvnorm : ‖(pv t : Limit) - 1‖ ≤ ‖(v : Limit) - 1‖ := by
        have h := Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le
          v t.2 hvTwo
        simpa [pv, Unitary.path] using h
      have hcommEq :
          (q t : Limit) * ofStage n c - ofStage n c * (q t : Limit) =
            (((pv t : Limit) - 1) * ofStage n c -
              ofStage n c * ((pv t : Limit) - 1)) * (u0 : Limit) := by
        change (((pv t : unitary Limit) * u0 : unitary Limit) : Limit) *
            ofStage n c - ofStage n c *
              ((((pv t : unitary Limit) * u0 : unitary Limit) : Limit)) = _
        simp only [Submonoid.coe_mul]
        noncomm_ring [(hcentral c).eq]
      rw [hcommEq, CStarRing.norm_mul_coe_unitary]
      calc
        _ ≤ ‖((pv t : Limit) - 1) * ofStage n c‖ +
            ‖ofStage n c * ((pv t : Limit) - 1)‖ := norm_sub_le _ _
        _ ≤ ‖(pv t : Limit) - 1‖ * ‖ofStage n c‖ +
            ‖ofStage n c‖ * ‖(pv t : Limit) - 1‖ := by
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖(pv t : Limit) - 1‖ * ‖ofStage n c‖ := by ring
        _ ≤ 2 * ‖(v : Limit) - 1‖ * ‖ofStage n c‖ := by
          gcongr
        _ ≤ epsilon * ‖ofStage n c‖ := by
          have hmul := mul_le_mul_of_nonneg_right hvhalf.le
            (norm_nonneg (ofStage n c))
          nlinarith
    intro t c
    have ht : p t ∈ Set.range p0 ∪ Set.range q := by
      rw [← Path.trans_range]
      exact ⟨t, rfl⟩
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [show p t = p0 s by exact hs.symm]
      exact hp0bound s c
    · rw [show p t = q s by exact hs.symm]
      exact hqbound s c

set_option maxHeartbeats 800000 in
/-- Endpoint compatibility form of exact stage transport.  The stronger
theorem above supplies a path with the same commutator bound at every time. -/
theorem exists_delta_exact_unitary_apply_eq_and_stage_commutator
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        rho (u : Limit) xi = eta ∧
        ∀ c : Stage n,
          ‖(u : Limit) * ofStage n c - ofStage n c * (u : Limit)‖ ≤
            epsilon * ‖ofStage n c‖ := by
  obtain ⟨delta, hdelta, hmain⟩ :=
    exists_delta_exact_unitary_path_apply_eq_and_stage_commutator
      rho hrho n hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  obtain ⟨u, huapply, p, hp⟩ := hmain xi eta hxi heta hstate
  refine ⟨u, huapply, ?_⟩
  intro c
  have h := hp (1 : Set.Icc (0 : ℝ) 1) c
  simpa only [p.target] using h

set_option maxHeartbeats 800000 in
/-- Local exact transport in path form for the alternating construction.
For a prescribed finite set, one stage and one entrywise state tolerance are
fixed first.  Any two unit vectors meeting those tests are related exactly by
an inner unitary, along a path whose forward and inverse conjugations are
uniformly small on the prescribed set at every time. -/
theorem exists_stageTests_exact_unitary_path_apply_eq_and_conjugate_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        rho (u : Limit) xi = eta ∧
        ∃ p : Path 1 u, ∀ t, ∀ a ∈ F,
          ‖(p t : Limit) * a * star (p t : Limit) - a‖ < epsilon ∧
          ‖star (p t : Limit) * a * (p t : Limit) - a‖ < epsilon := by
  classical
  let M : ℝ := (∑ a ∈ F, ‖a‖) + epsilon / 8 + 1
  have hsum : 0 ≤ ∑ a ∈ F, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 < M := by
    dsimp only [M]
    linarith
  obtain ⟨n, hn⟩ := exists_common_stage_approx F
    (show 0 < epsilon / 8 by positivity)
  let gamma : ℝ := epsilon / (4 * M)
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    positivity
  obtain ⟨delta, hdelta, hlocal⟩ :=
    exists_delta_exact_unitary_path_apply_eq_and_stage_commutator
      rho hrho n hgamma
  refine ⟨n, delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  obtain ⟨u, huapply, p, hcomm⟩ := hlocal xi eta hxi heta hstate
  refine ⟨u, huapply, p, ?_⟩
  intro t a ha
  let ut : unitary Limit := p t
  obtain ⟨c, hc⟩ := hn a ha
  have haSum : ‖a‖ ≤ ∑ x ∈ F, ‖x‖ :=
    Finset.single_le_sum (fun x _ => norm_nonneg x) ha
  have hcM : ‖ofStage n c‖ < M := by
    calc
      ‖ofStage n c‖ = ‖a - (a - ofStage n c)‖ := by
        congr 1
        module
      _ ≤ ‖a‖ + ‖a - ofStage n c‖ := norm_sub_le _ _
      _ < ‖a‖ + epsilon / 8 := by linarith
      _ ≤ (∑ x ∈ F, ‖x‖) + epsilon / 8 := by
        simpa only [add_comm] using add_le_add_right haSum (epsilon / 8)
      _ < M := by dsimp only [M]; linarith
  have hgammaM : gamma * ‖ofStage n c‖ < epsilon / 4 := by
    calc
      _ < gamma * M := mul_lt_mul_of_pos_left hcM hgamma
      _ = epsilon / 4 := by
        dsimp only [gamma]
        field_simp
  have hcommA :
      ‖(ut : Limit) * a - a * (ut : Limit)‖ < epsilon := by
    have hdecomp :
        (ut : Limit) * a - a * (ut : Limit) =
          (ut : Limit) * (a - ofStage n c) +
            ((ut : Limit) * ofStage n c - ofStage n c * (ut : Limit)) +
              (ofStage n c - a) * (ut : Limit) := by noncomm_ring
    rw [hdecomp]
    calc
      _ ≤ ‖(ut : Limit) * (a - ofStage n c)‖ +
          ‖(ut : Limit) * ofStage n c - ofStage n c * (ut : Limit)‖ +
            ‖(ofStage n c - a) * (ut : Limit)‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)
      _ = ‖a - ofStage n c‖ +
          ‖(ut : Limit) * ofStage n c - ofStage n c * (ut : Limit)‖ +
            ‖ofStage n c - a‖ := by
        rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary]
      _ ≤ ‖a - ofStage n c‖ + gamma * ‖ofStage n c‖ +
            ‖ofStage n c - a‖ := by
        gcongr
        exact hcomm t c
      _ < epsilon := by
        rw [norm_sub_rev (ofStage n c) a]
        nlinarith
  have hconj :
      (ut : Limit) * a * star (ut : Limit) - a =
        ((ut : Limit) * a - a * (ut : Limit)) * star (ut : Limit) := by
    symm
    calc
        ((ut : Limit) * a - a * (ut : Limit)) * star (ut : Limit) =
          ((ut : Limit) * a) * star (ut : Limit) -
            (a * (ut : Limit)) * star (ut : Limit) := sub_mul _ _ _
      _ = (ut : Limit) * a * star (ut : Limit) - a := by
        have huunit : (ut : Limit) * star (ut : Limit) = 1 :=
          Unitary.mul_star_self_of_mem ut.property
        rw [mul_assoc a (ut : Limit) (star (ut : Limit)), huunit, mul_one]
  constructor
  · rw [hconj]
    have hstar : star (ut : Limit) = ((star ut : unitary Limit) : Limit) := rfl
    rw [hstar, CStarRing.norm_mul_coe_unitary]
    exact hcommA
  · have hconjInv :
        star (ut : Limit) * a * (ut : Limit) - a =
          star (ut : Limit) * (a * (ut : Limit) - (ut : Limit) * a) := by
      have huunit : star (ut : Limit) * (ut : Limit) = 1 :=
        Unitary.star_mul_self_of_mem ut.property
      symm
      calc
        star (ut : Limit) * (a * (ut : Limit) - (ut : Limit) * a) =
            star (ut : Limit) * (a * (ut : Limit)) -
              star (ut : Limit) * ((ut : Limit) * a) := mul_sub _ _ _
        _ = (star (ut : Limit) * a) * (ut : Limit) -
              (star (ut : Limit) * (ut : Limit)) * a := by
            rw [mul_assoc, mul_assoc]
        _ = star (ut : Limit) * a * (ut : Limit) - a := by
            rw [huunit, one_mul]
    rw [hconjInv]
    have hstar : star (ut : Limit) = ((star ut : unitary Limit) : Limit) := rfl
    rw [hstar, CStarRing.norm_coe_unitary_mul]
    rw [show a * (ut : Limit) - (ut : Limit) * a =
        -((ut : Limit) * a - a * (ut : Limit)) by module, norm_neg]
    exact hcommA

set_option maxHeartbeats 800000 in
/-- Endpoint compatibility form of finite-set exact local transport. -/
theorem exists_stageTests_exact_unitary_apply_eq_and_conjugate_sub_norm_lt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (rho : Representation Limit H) (hrho : StarAlgHom.IsIrreducible rho)
    (F : Finset Limit) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ n, ∃ delta > 0, ∀ (xi eta : H), ‖xi‖ = 1 → ‖eta‖ = 1 →
      (∀ i j : Fin (2 ^ n),
        ‖Representation.vectorFunctional rho xi (limitMatrixUnit n i j) -
          Representation.vectorFunctional rho eta (limitMatrixUnit n i j)‖ < delta) →
      ∃ u : unitary Limit,
        rho (u : Limit) xi = eta ∧
        ∀ a ∈ F,
          ‖(u : Limit) * a * star (u : Limit) - a‖ < epsilon ∧
          ‖star (u : Limit) * a * (u : Limit) - a‖ < epsilon := by
  obtain ⟨n, delta, hdelta, hmain⟩ :=
    exists_stageTests_exact_unitary_path_apply_eq_and_conjugate_sub_norm_lt
      rho hrho F hepsilon
  refine ⟨n, delta, hdelta, ?_⟩
  intro xi eta hxi heta hstate
  obtain ⟨u, huapply, p, hp⟩ := hmain xi eta hxi heta hstate
  refine ⟨u, huapply, ?_⟩
  intro a ha
  have h := hp (1 : Set.Icc (0 : ℝ) 1) a ha
  simpa only [p.target] using h

end MathlibAnnex.CStarAlgebra.CAR
