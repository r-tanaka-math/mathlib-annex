import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CommutantRetraction

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra ComplexOrder
open MathlibAnnex.CStarAlgebra.CAR

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (H →L[ℂ] H) →P[ℂ]
      (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra :=
  commutantRetraction rho

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) : commutantRetraction rho 1 = 1 :=
  commutantRetraction_one rho

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra) :
    commutantRetraction rho (S : H →L[ℂ] H) = S := commutantRetraction_restrict rho S

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S T : (VonNeumannAlgebra.generated rho.range).commutant.toStarSubalgebra)
    (b : H →L[ℂ] H) :
    commutantRetraction rho ((S : H →L[ℂ] H) * b * (T : H →L[ℂ] H)) =
      S * commutantRetraction rho b * T := commutantRetraction_mul_mul rho S T b

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : H →L[ℂ] H) :
    commutantRetraction rho (commutantRetraction rho b : H →L[ℂ] H) =
      commutantRetraction rho b := commutantRetraction_idempotent rho b

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : H →L[ℂ] H) :
    star (commutantRetraction rho b) * commutantRetraction rho b ≤
      commutantRetraction rho (star b * b) := star_mul_commutantRetraction_le rho b

example (rho : Limit →⋆ₐ[ℂ] (H →L[ℂ] H)) (b : H →L[ℂ] H) :
    ‖commutantRetraction rho b‖ ≤ ‖b‖ := norm_commutantRetraction_le rho b
