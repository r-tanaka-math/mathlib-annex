import MathlibAnnex.Analysis.VonNeumannAlgebra.TypeI.Factor
import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.CentralSplit

/-! Direct consumers of the internal type I and central-support interfaces. -/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

open VonNeumannAlgebra

example (M : VonNeumannAlgebra H) (hI : IsTypeI M)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q * p = q ∧
      ∀ a b : M.toStarSubalgebra,
        q * a = a → a * q = a → q * b = b → b * q = b → a * b = b * a := by
  obtain ⟨q, hq, hq0, hqp⟩ := hI p hp hp0
  exact ⟨q, hq.1, hq0, hqp, hq.2⟩

example (M : VonNeumannAlgebra H) : IsAbelianProjection M 0 :=
  isAbelianProjection_zero (M := M)

example (M : VonNeumannAlgebra H) [Subsingleton M.toStarSubalgebra] : IsTypeI M :=
  isTypeI_of_subsingleton (M := M)

example (M : VonNeumannAlgebra H)
    (hcomm : ∀ a b : M.toStarSubalgebra, a * b = b * a) : IsTypeI M :=
  isTypeI_of_commutative (M := M) hcomm

example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (hp : IsAbelianProjection M p) (heq : MurrayVonNeumannEquivalent p q) :
    ∀ a b : corner M q heq.2.1, a * b = b * a :=
  (isAbelianProjection_iff_corner_commutative M q heq.2.1).mp (hp.of_equivalent heq)

example (M : VonNeumannAlgebra H) (p : M.toStarSubalgebra) :
    ∃ z : M.toStarSubalgebra, IsStarProjection z ∧ z * p = p ∧
      (∀ a : M.toStarSubalgebra, a * z = z * a) ∧
      ∀ q : M.toStarSubalgebra, IsStarProjection q →
        (∀ a : M.toStarSubalgebra, a * q = q * a) → q * p = p → z * q = z := by
  refine ⟨centralSupport M p, isStarProjection_centralSupport M p,
    centralSupport_mul_self M p, centralSupport_commute M p, ?_⟩
  intro q hq hqc hqp
  exact centralSupport_le (M := M) (p := p) (q := q) hq hqc hqp

example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (h : MurrayVonNeumannEquivalent p q) : centralSupport M p = centralSupport M q :=
  centralSupport_eq_of_equivalent (M := M) (p := p) (q := q) h

example (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : centralSupport M p * centralSupport M q ≠ 0) :
    ∃ p' q' : M.toStarSubalgebra, p' ≠ 0 ∧ q' ≠ 0 ∧ p' ≤ p ∧ q' ≤ q ∧
      ∃ v : M.toStarSubalgebra,
        IsPartialIsometry v ∧ star v * v = p' ∧ v * star v = q' := by
  obtain ⟨p', q', heq, hp'0, hq'0, hp'p, hq'q⟩ :=
    exists_nonzero_equivalent_subprojections_of_centralSupport_mul_ne_zero M hp hq h
  exact ⟨p', q', hp'0, hq'0, hp'p, hq'q, heq.2.2⟩

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M) (hI : IsTypeI M) :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 ∧ centralSupport M p = 1 :=
  hfactor.exists_nonzero_abelian_projection hI

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M) (hI : IsTypeI M) :
    ∃ p : M.toStarSubalgebra, IsAbelianProjection M p ∧ p ≠ 0 ∧
      (∀ q : M.toStarSubalgebra, IsStarProjection q → q ≠ 0 → q ≤ p → q = p) ∧
      centralSupport M p = 1 := by
  obtain ⟨p, hp, hmin, hc⟩ := hfactor.exists_minimal_abelian_projection hI
  exact ⟨p, hp, hmin.2.1, hmin.2.2, hc⟩

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (p r : M.toStarSubalgebra) (hp : IsAbelianProjection M p) (hp0 : p ≠ 0)
    (hr : IsStarProjection r) (hr0 : r ≠ 0) :
    ∃ q : M.toStarSubalgebra, q ≠ 0 ∧ q ≤ r ∧
      ∃ v : M.toStarSubalgebra,
        IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨q, heq, hq0, hqr⟩ :=
    hfactor.exists_equivalent_subprojection_of_minimal_projection
      (hp.isMinimalStarProjection_of_isFactor hp0 hfactor) hr hr0
  exact ⟨q, hq0, hqr, heq.2.2⟩

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (p : M.toStarSubalgebra) (hp : IsAbelianProjection M p) (hp0 : p ≠ 0) :
    IsTypeI M :=
  hfactor.isTypeI_iff_exists_nonzero_abelian_projection.mpr ⟨p, hp, hp0⟩

example (M : VonNeumannAlgebra H) (hfactor : IsFactor M)
    (p a : M.toStarSubalgebra) (hp : IsAbelianProjection M p) (hp0 : p ≠ 0) :
    ∃ c : ℂ, p * a * p = c • p :=
  hp.exists_scalar_corner_of_isFactor hp0 hfactor a

example : IsTypeI (generated (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))) :=
  isTypeI_generated_top (H := H)

example (M : VonNeumannAlgebra H) (hfull : ∀ T : H →L[ℂ] H, T ∈ M)
    (p : M.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : M.toStarSubalgebra, IsAbelianProjection M q ∧ q ≠ 0 ∧ q ≤ p := by
  obtain ⟨q, hq, hq0, hqp⟩ := isTypeI_of_all_operators_mem M hfull p hp hp0
  exact ⟨q, hq, hq0, (hq.1.le_iff_mul_eq_left hp).mpr hqp⟩

example (M : VonNeumannAlgebra H) :
    ∀ p : M.toStarSubalgebra, IsAbelianProjection M p →
      p * (1 - abelianCentralSupport M) = p → p = 0 := by
  intro p hp hpc
  exact eq_zero_of_abelian_of_mul_complement_eq hp hpc

example (M : VonNeumannAlgebra H) :
    IsTypeIProjection M (abelianCentralSupport M) :=
  isTypeIProjection_abelianCentralSupport M

example (M : VonNeumannAlgebra H) :
    Nonempty (M.toStarSubalgebra ≃⋆ₐ[ℂ]
      (corner M (abelianCentralSupport M) (isStarProjection_abelianCentralSupport M) ×
       corner M (1 - abelianCentralSupport M)
         (isStarProjection_abelianCentralSupport M).one_sub)) :=
  ⟨centralCornerProdEquiv M (abelianCentralSupport M)
    (isStarProjection_abelianCentralSupport M) (abelianCentralSupport_commute M)⟩

example (M : VonNeumannAlgebra H) (z : M.toStarSubalgebra)
    (hz : IsTypeIProjection M z)
    (hcentral : ∀ a : M.toStarSubalgebra, a * z = z * a)
    (hcomp : ∀ p : M.toStarSubalgebra, IsAbelianProjection M p →
      p * (1 - z) = p → p = 0) : z = abelianCentralSupport M :=
  eq_abelianCentralSupport_of_type_i_decomposition
    (M := M) (z := z) hz hcentral hcomp

example {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) (hM : IsTypeI M) : IsTypeI N :=
  hM.map (M := M) (N := N) e
