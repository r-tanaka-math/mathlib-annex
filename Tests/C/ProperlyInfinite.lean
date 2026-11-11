import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.ProperlyInfinite

/-!
Typed consumers for proper infiniteness. Projection witnesses belong to the
specified algebra, and the proper corner witness has initial projection
equal to its actual unit p.
-/

set_option autoImplicit false
noncomputable section

open VonNeumannAlgebra
open scoped CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsTypeIIIProjection M p) (hp0 : p ≠ 0) :
    IsProperlyInfiniteProjection p :=
  hp.isProperlyInfiniteProjection hp0

/-- The two witnesses are internal, including both support equations. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsTypeIIIProjection M p) (hp0 : p ≠ 0) :
    ∃ v w : M.toStarSubalgebra,
      IsPartialIsometry v ∧ IsPartialIsometry w ∧
      star v * v = p ∧ star w * w = p ∧
      (v * star v) * p = v * star v ∧
      (w * star w) * p = w * star w ∧
      (v * star v) * (w * star w) = 0 := by
  obtain ⟨_, _, r, s, hpr, hps, hrp, hsp, hrs⟩ :=
    hp.isProperlyInfiniteProjection hp0
  obtain ⟨v, hv, hvi, hvf⟩ := hpr.exists_partial_isometry
  obtain ⟨w, hw, hwi, hwf⟩ := hps.exists_partial_isometry
  refine ⟨v, w, hv, hw, hvi, hwi, ?_, ?_, ?_⟩
  · simpa only [hvf] using hrp
  · simpa only [hwf] using hsp
  · simpa only [hvf, hwf] using hrs

/-- Endpoint absorption places the same witnesses in pMp. Its unit is p. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsTypeIIIProjection M p) (hp0 : p ≠ 0) :
    ∃ v w : corner M p hp.1,
      IsPartialIsometry v ∧ IsPartialIsometry w ∧
      star v * v = cornerUnit M p hp.1 ∧
      star w * w = cornerUnit M p hp.1 ∧
      (v * star v) * (w * star w) = 0 := by
  obtain ⟨_, _, r, s, hpr, hps, hrp, hsp, hrs⟩ :=
    hp.isProperlyInfiniteProjection hp0
  obtain ⟨v, hv, hvi, hvf, hpv, hvp⟩ :=
    hpr.exists_partial_isometry_with_absorption hp.1 hp.1.isIdempotentElem.eq hrp
  obtain ⟨w, hw, hwi, hwf, hpw, hwp⟩ :=
    hps.exists_partial_isometry_with_absorption hp.1 hp.1.isIdempotentElem.eq hsp
  let v' : corner M p hp.1 := ⟨v, hpv, hvp⟩
  let w' : corner M p hp.1 := ⟨w, hpw, hwp⟩
  have hv' : IsPartialIsometry v' := by
    apply Subtype.ext
    exact hv
  have hw' : IsPartialIsometry w' := by
    apply Subtype.ext
    exact hw
  refine ⟨v', w', hv', hw', Subtype.ext hvi, Subtype.ext hwi, ?_⟩
  apply Subtype.ext
  change (v * star v) * (w * star w) = 0
  rw [hvf, hwf]
  exact hrs

example (M : VonNeumannAlgebra H) (hM : IsTypeIII M)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    IsProperlyInfiniteProjection p :=
  hM.isProperlyInfiniteProjection hp hp0

/-- Nonfiniteness alone supplies a properly infinite subprojection. -/
example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hfinite : ¬ IsFiniteProjection p) :
    ∃ e : M.toStarSubalgebra, IsProperlyInfiniteProjection e ∧ e ≤ p :=
  exists_isProperlyInfiniteProjection_le_of_not_isFiniteProjection M hp hfinite

/-- The index universe is arbitrary; there is no enumeration hypothesis. -/
example (M : VonNeumannAlgebra H) {ι : Type v}
    (P : ι → M.toStarSubalgebra)
    (hP : ∀ i, IsProperlyInfiniteProjection (P i))
    (horth : Pairwise (fun i j ↦ P i * P j = 0))
    (hne : iSupProjection M P (fun i ↦ (hP i).1) ≠ 0) :
    IsProperlyInfiniteProjection (iSupProjection M P (fun i ↦ (hP i).1)) :=
  isProperlyInfiniteProjection_iSupProjection M P hP horth hne

/-- A zero type III component is allowed, whereas proper infiniteness is nonzero. -/
example (M : VonNeumannAlgebra H) :
    IsTypeIIIProjection M (0 : M.toStarSubalgebra) ∧
      ¬ IsProperlyInfiniteProjection (0 : M.toStarSubalgebra) := by
  constructor
  · refine ⟨IsStarProjection.zero _, ?_⟩
    intro q _ hq
    simpa only [mul_zero] using hq.symm
  · intro h
    exact h.ne_zero rfl

example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra)
    (hp : IsFiniteProjection p) : ¬ IsProperlyInfiniteProjection p :=
  hp.not_isProperlyInfiniteProjection

/-- The canonical type III central component consumes the same theorem. -/
example (M : VonNeumannAlgebra H) (h : typeIIIProjection M ≠ 0) :
    IsProperlyInfiniteProjection (typeIIIProjection M) :=
  (isTypeIIIProjection_typeIIIProjection M).isProperlyInfiniteProjection h
