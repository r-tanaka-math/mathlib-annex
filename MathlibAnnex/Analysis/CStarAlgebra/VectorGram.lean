import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# Gram matrices from vector functionals

This file fixes the star/order convention used by finite-row pure-state
transport.  Mathlib's complex inner product is conjugate-linear in the first
variable, so the vectors `π(xᵢ*)ξ` have Gram entry given by the vector
functional at `xᵢ xⱼ*`.
-/

set_option autoImplicit false

open scoped InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact Gram entry for the pulled-back vector family
`i ↦ π(star (x i)) ξ`. -/
theorem inner_map_star_apply (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (x y : A) :
    inner ℂ (pi (star x) ξ) (pi (star y) ξ) =
      vectorFunctional pi ξ (x * star y) := by
  simpa only [star_star] using
    (vectorFunctional_star_mul pi ξ (star x) (star y)).symm

/-- Moving the vector by `π(x*)` conjugates the argument in the displayed
orientation.  This lemma makes the star direction in exact state transport
explicit. -/
theorem vectorFunctional_map_star (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (x a : A) :
    vectorFunctional pi (pi (star x) ξ) a =
      vectorFunctional pi ξ (x * a * star x) := by
  calc
    vectorFunctional pi (pi (star x) ξ) a =
        inner ℂ (pi (star x) ξ) (pi (a * star x) ξ) := by
      rw [vectorFunctional_apply, map_mul]
      rfl
    _ = vectorFunctional pi ξ (star (star x) * (a * star x)) := by
      exact (vectorFunctional_star_mul pi ξ (star x) (a * star x)).symm
    _ = vectorFunctional pi ξ (x * a * star x) := by
      simp only [star_star, mul_assoc]

/-- A finite family of vector-functional values is exactly the Gram matrix
of the corresponding represented pullback vectors. -/
theorem inner_map_star_family (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {n : ℕ} (x : Fin n → A) (i j : Fin n) :
    inner ℂ (pi (star (x i)) ξ) (pi (star (x j)) ξ) =
      vectorFunctional pi ξ (x i * star (x j)) :=
  inner_map_star_apply pi ξ (x i) (x j)

/-- The finite sum of diagonal Gram entries is the vector-functional value
of the row support `Σ xᵢxᵢ*`. -/
theorem sum_inner_map_star_self (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {n : ℕ} (x : Fin n → A) :
    ∑ i, inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ) =
      vectorFunctional pi ξ (∑ i, x i * star (x i)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_map_star_apply pi ξ (x i) (x i)

/-- Exact row normalization gives exact total squared norm in every unital
representation. -/
theorem sum_norm_sq_map_star_eq (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    {n : ℕ} (x : Fin n → A) (hx : ∑ i, x i * star (x i) = 1) :
    ∑ i, ‖pi (star (x i)) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  calc
    ∑ i, ‖pi (star (x i)) ξ‖ ^ 2 =
        ∑ i, (inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ)).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact norm_sq_eq_re_inner (𝕜 := ℂ) (pi (star (x i)) ξ)
    _ = (∑ i, inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ)).re := by
      symm
      simpa using
        (Complex.re_sum (Finset.univ : Finset (Fin n))
          (fun i => inner ℂ (pi (star (x i)) ξ) (pi (star (x i)) ξ)))
    _ = (vectorFunctional pi ξ (∑ i, x i * star (x i))).re := by
      rw [sum_inner_map_star_self]
    _ = (inner ℂ ξ ξ).re := by
      simp only [hx, vectorFunctional_apply, map_one, one_apply_eq_self]
    _ = ‖ξ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm

end MathlibAnnex.Analysis.CStarAlgebra.Representation
