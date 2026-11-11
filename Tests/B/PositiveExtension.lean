import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveExtension

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) (ha : 0 ≤ a) :
    0 ≤ Representation.compression (rho := rho) (U := U) a :=
  (Representation.compression rho U).map_nonneg ha

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    ‖Representation.compression rho U a‖ ≤ ‖a‖ :=
  Representation.norm_compression_le (rho := rho) (U := U) (a := a)

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) :
    Representation.compression rho U 1 = 1 :=
  Representation.compression_one (rho := rho) (U := U)

example (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    Representation.compression rho U (star a) =
      star (Representation.compression rho U a) :=
  map_star (Representation.compression rho U) a

example (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (pi : Representation D H) (rho : Representation A K) (U : H →ₗᵢ[ℂ] K)
    (hU : ∀ (d : D) x, U (pi d x) = rho (d : A) (U x))
    (d e : D) (a : A) :
    Representation.compression rho U ((d : A) * a * (e : A)) =
      pi d * Representation.compression rho U a * pi e :=
  Representation.compression_mul_mul (D := D) (pi := pi) (rho := rho)
    (U := U) (hU := hU) (d := d) (e := e) (a := a)

example (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (pi : Representation D H) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi)) :
    ∃ P : A →P[ℂ] (H →L[ℂ] H), P 1 = 1 ∧
      (∀ d : D, P (d : A) = pi d) ∧
      ∀ (d e : D) (a : A),
        P ((d : A) * a * (e : A)) = pi d * P a * pi e := by
  obtain ⟨P, h1, -, -, hD, hmul⟩ :=
    Representation.exists_positive_bimodule_extension
      (D := D) (pi := pi) (xi := xi) (hxi := hxi) (hcyclic := hcyclic)
  exact ⟨P, h1, hD, hmul⟩

-- The auxiliary map has only positivity, restriction and bimodule inputs.
-- In particular this consumer has no normality argument or normality class.
example {B : Type z} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (pi : Representation D H) (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi))
    (sigma : D →⋆ₐ[ℂ] B) (E : (H →L[ℂ] H) →ₚ[ℂ] B)
    (hEpi : ∀ d : D, E (pi d) = sigma d)
    (hEbimodule : ∀ (d e : D) (T : H →L[ℂ] H),
      E (pi d * T * pi e) = sigma d * E T * sigma e) :
    ∃ P : A →P[ℂ] B, P 1 = 1 ∧
      (∀ a : A, P (star a) = star (P a)) ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      ∀ (d e : D) (a : A),
        P ((d : A) * a * (e : A)) = sigma d * P a * sigma e :=
  Representation.exists_positive_bimodule_extension_of_positive_map
    (D := D) (pi := pi) (xi := xi) (hxi := hxi) (hcyclic := hcyclic)
    (sigma := sigma) (E := E) (hEpi := hEpi) (hEbimodule := hEbimodule)

-- Compression includes the zero Hilbert space without imposing Nontrivial.
example [Subsingleton H] (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    Representation.compression rho U a = 0 :=
  Subsingleton.elim _ _
