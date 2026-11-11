import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.SchroederBernstein

set_option autoImplicit false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The sandwich consumer starts with an explicit witness in `M` and
returns another actual internal witness for the intermediate projection. -/
example (M : VonNeumannAlgebra H) {p q r : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (v : M.toStarSubalgebra) (hi : star v * v = p) (hf : v * star v = r)
    (hrq : r * q = r) (hqp : q * p = q) :
    ∃ w : M.toStarSubalgebra,
      IsPartialIsometry w ∧ star w * w = p ∧ w * star w = q := by
  have hpr : MurrayVonNeumannEquivalent p r :=
    murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp, hr, v, hi, hf⟩
  exact (VonNeumannAlgebra.murrayVonNeumannEquivalent_of_sandwich
    (M := M) (p := p) (q := q) (r := r)
    (hpr := hpr) (hq := hq) (hrq := hrq) (hqp := hqp)).exists_partial_isometry

/-- Both subequivalence witnesses and both intermediate projections are
explicitly carried by the specified algebra. -/
example (M : VonNeumannAlgebra H) {p q r s : M.toStarSubalgebra}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (v w : M.toStarSubalgebra)
    (hvi : star v * v = p) (hvf : v * star v = r) (hrq : r * q = r)
    (hwi : star w * w = q) (hwf : w * star w = s) (hsp : s * p = s) :
    ∃ u : M.toStarSubalgebra,
      IsPartialIsometry u ∧ star u * u = p ∧ u * star u = q := by
  have hpr : MurrayVonNeumannEquivalent p r :=
    murrayVonNeumannEquivalent_iff_exists.mpr ⟨hp, hr, v, hvi, hvf⟩
  have hqs : MurrayVonNeumannEquivalent q s :=
    murrayVonNeumannEquivalent_iff_exists.mpr ⟨hq, hs, w, hwi, hwf⟩
  exact (VonNeumannAlgebra.murrayVonNeumannEquivalent_of_mutual_subequivalent
    (M := M) (p := p) (q := q)
    (hpq := ⟨hq, r, hpr, hrq⟩) (hqp := ⟨hp, s, hqs, hsp⟩)).exists_partial_isometry

/-- The same theorem includes the zero projection without a nonzero
hypothesis or an ambient-factor hypothesis. -/
example (M : VonNeumannAlgebra H) {q : M.toStarSubalgebra}
    (h0q : MurrayVonNeumannSubequivalent (0 : M.toStarSubalgebra) q)
    (hq0 : MurrayVonNeumannSubequivalent q (0 : M.toStarSubalgebra)) : q = 0 :=
  (VonNeumannAlgebra.murrayVonNeumannEquivalent_of_mutual_subequivalent
    (M := M) (p := 0) (q := q) (hpq := h0q) (hqp := hq0)).eq_zero_iff.mp rfl

example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra) :
    MurrayVonNeumannEquivalent p q ↔
      MurrayVonNeumannSubequivalent p q ∧ MurrayVonNeumannSubequivalent q p :=
  VonNeumannAlgebra.murrayVonNeumannEquivalent_iff_mutual_subequivalent
    (M := M) (p := p) (q := q)
