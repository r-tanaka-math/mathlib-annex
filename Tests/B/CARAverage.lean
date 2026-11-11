import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.CARAverage

set_option autoImplicit false
noncomputable section

open scoped ComplexOrder
open MathlibAnnex.CStarAlgebra.CAR

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) : B →P[ℂ] B :=
  representedRowAverage rho n

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) : representedRowAverage rho n 1 = 1 :=
  representedRowAverage_one rho n

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (b : B) (hb : 0 ≤ b) :
    0 ≤ representedRowAverage rho n b := map_nonneg _ hb

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (k l : Fin (2 ^ n)) (b : B) :
    rho (limitMatrixUnit n k l) * representedRowAverage rho n b =
      representedRowAverage rho n b * rho (limitMatrixUnit n k l) :=
  limitMatrixUnit_commute_representedRowAverage rho n k l b

example (rho : Limit →⋆ₐ[ℂ] B) {n m : ℕ} (h : n ≤ m) (c : Stage n) (b : B) :
    rho (ofStage n c) * representedRowAverage rho m b =
      representedRowAverage rho m b * rho (ofStage n c) :=
  ofStage_commute_representedRowAverage_of_le rho h c b

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (S : B)
    (hS : ∀ a : Limit, rho a * S = S * rho a) : representedRowAverage rho n S = S :=
  representedRowAverage_eq_self rho n S hS

example (rho : Limit →⋆ₐ[ℂ] B) (n : ℕ) (S T b : B)
    (hS : ∀ a : Limit, rho a * S = S * rho a)
    (hT : ∀ a : Limit, rho a * T = T * rho a) :
    representedRowAverage rho n (S * b * T) = S * representedRowAverage rho n b * T :=
  representedRowAverage_mul_mul rho n S T b hS hT
