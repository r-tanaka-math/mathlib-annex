import MathlibAnnex.Analysis.VonNeumannAlgebra.Projection.SpectralCutoff

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra

namespace MathlibAnnex.Tests

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (M : VonNeumannAlgebra H)

example (x y : M.toStarSubalgebra) (hxy : x * y = 0) :
    VonNeumannAlgebra.rightSupport M x * y = 0 :=
  (VonNeumannAlgebra.rightSupport_mul_eq_zero_iff M x y).2 hxy

example (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    VonNeumannAlgebra.leftSupport M x⁺ * x = x⁺ :=
  VonNeumannAlgebra.leftSupport_posPart_mul M x hx

example (h : M.toStarSubalgebra) (ε : ℝ) :
    IsStarProjection (VonNeumannAlgebra.spectralCutoff M h ε) :=
  VonNeumannAlgebra.isStarProjection_spectralCutoff M h ε

example (h : M.toStarSubalgebra) (ε : ℝ) (hh : IsSelfAdjoint h) :
    Commute (VonNeumannAlgebra.spectralCutoff M h ε) h :=
  VonNeumannAlgebra.commute_spectralCutoff M h ε hh

example (h : M.toStarSubalgebra) (ε : ℝ) (hh : 0 ≤ h) :
    ε • VonNeumannAlgebra.spectralCutoff M h ε ≤ h :=
  VonNeumannAlgebra.smul_spectralCutoff_le M h ε hh

example (h : M.toStarSubalgebra) (hh : 0 ≤ h) (hne : h ≠ 0) :
    ∃ (ε : ℝ) (p : M.toStarSubalgebra), 0 < ε ∧ IsStarProjection p ∧
      p ≠ 0 ∧ Commute p h ∧ ε • p ≤ h :=
  VonNeumannAlgebra.exists_nonzero_projection_smul_le M h hh hne

example {p h : M.toStarSubalgebra} (hp : IsStarProjection p)
    {ε : ℝ} (hε : 0 < ε) (hle : ε • p ≤ h) :
    IsUnit (p * h * p + (1 - p)) :=
  VonNeumannAlgebra.isUnit_sandwich_add_one_sub M hp hε hle

example {p h : M.toStarSubalgebra} (hp : IsStarProjection p)
    {ε : ℝ} (hε : 0 < ε) (hle : ε • p ≤ h) :
    Ring.inverse (p * h * p + (1 - p)) * p * h * p = p :=
  VonNeumannAlgebra.ringInverse_sandwich_add_one_sub_mul M hp
    (VonNeumannAlgebra.isUnit_sandwich_add_one_sub M hp hε hle)

example {p h a : M.toStarSubalgebra} (hp : IsStarProjection p)
    {ε : ℝ} (hε : 0 < ε) (hle : ε • p ≤ h) (hpa : p * a = a) :
    Ring.inverse (p * h * p + (1 - p)) * p * h * a = a :=
  VonNeumannAlgebra.ringInverse_sandwich_add_one_sub_mul_of_mul_eq_right M hp
    (VonNeumannAlgebra.isUnit_sandwich_add_one_sub M hp hε hle) hpa

end MathlibAnnex.Tests
