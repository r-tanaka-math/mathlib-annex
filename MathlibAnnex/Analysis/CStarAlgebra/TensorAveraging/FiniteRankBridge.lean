import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteRow
import MathlibAnnex.Analysis.LocallyConvex.FiniteApproximation

/-!
# A finite-rank approximate-identity bridge

The bidual hypothesis in this file is deliberately conditional.  It consists
only of weak-star convex-hull membership, tensor left/right centrality, and
the stated vector moments.  No global row supplier or sequence is assumed.
-/

set_option autoImplicit false

open scoped CStarAlgebra InnerProductSpace ComplexConjugate

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

open MathlibAnnex.ProjectiveTensorProduct
open MathlibAnnex.ProjectiveTensorProduct.Algebra
open MathlibAnnex.FiniteApproximation

universe uA uH

noncomputable section

variable (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A C*-representation, viewed only as its contractive continuous linear map. -/
def representationCLM (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := ρ
      map_add' := map_add ρ
      map_smul' := map_smul ρ }
    1 fun a ↦ by
    change ‖ρ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ρ a

@[simp]
theorem representationCLM_apply (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    representationCLM A H ρ a = ρ a := rfl

/-- The represented multiplication map on the projective tensor square. -/
def representedProduct (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Tensor A →L[ℂ] (H →L[ℂ] H) :=
  (representationCLM A H ρ).comp (multiplication ℂ A)

@[simp]
theorem representedProduct_tprod (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x y : A) :
    representedProduct A H ρ (tprod ℂ A A x y) = ρ (x * y) := by
  simp [representedProduct]

/-- The vector moment `t ↦ ⟪ξ, ρ(p(t)) ξ⟫`. -/
def vectorMoment (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    StrongDual ℂ (Tensor A) :=
  (innerSL ℂ ξ).comp
    ((ContinuousLinearMap.apply ℂ H ξ).comp (representedProduct A H ρ))

@[simp]
theorem vectorMoment_apply (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (t : Tensor A) :
    vectorMoment A H ρ ξ t = inner ℂ ξ (representedProduct A H ρ t ξ) := rfl

/-- A general represented matrix coefficient. -/
def matrixCoefficient (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    StrongDual ℂ (Tensor A) :=
  (innerSL ℂ η).comp
    ((ContinuousLinearMap.apply ℂ H ξ).comp (representedProduct A H ρ))

@[simp]
theorem matrixCoefficient_apply (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H)
    (t : Tensor A) :
    matrixCoefficient A H ρ η ξ t = inner ℂ η (representedProduct A H ρ t ξ) := rfl

/-- Polarization in the convention where the inner product is linear in its
second variable. -/
private theorem inner_map_polarization_right (T : H →L[ℂ] H) (x y : H) :
    inner ℂ x (T y) = (4 : ℂ)⁻¹ *
      (inner ℂ (x + y) (T (x + y)) - inner ℂ (x - y) (T (x - y)) -
        Complex.I * inner ℂ (x + Complex.I • y) (T (x + Complex.I • y)) +
        Complex.I * inner ℂ (x - Complex.I • y) (T (x - Complex.I • y))) := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem matrixCoefficient_polarization
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    matrixCoefficient A H ρ η ξ = (4 : ℂ)⁻¹ •
      (vectorMoment A H ρ (η + ξ) - vectorMoment A H ρ (η - ξ) -
        Complex.I • vectorMoment A H ρ (η + Complex.I • ξ) +
        Complex.I • vectorMoment A H ρ (η - Complex.I • ξ)) := by
  apply ContinuousLinearMap.ext
  intro t
  simp only [matrixCoefficient_apply, smul_apply, sub_apply, add_apply,
    vectorMoment_apply]
  rw [inner_map_polarization_right]
  ring

/-- Diagonal vector moments determine every represented matrix coefficient. -/
theorem omega_matrixCoefficient
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (hmoment : ∀ ξ : H, omega (vectorMoment A H ρ ξ) = (‖ξ‖ ^ 2 : ℂ))
    (η ξ : H) :
    omega (matrixCoefficient A H ρ η ξ) = inner ℂ η ξ := by
  rw [matrixCoefficient_polarization]
  simp only [map_smul, map_add, map_sub, hmoment]
  simpa [inner_self_eq_norm_sq_to_K] using
    (inner_map_polarization_right H (ContinuousLinearMap.id ℂ H) η ξ).symm

/-- Applying the represented product to one vector. -/
def representedVector (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Tensor A →L[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H ξ).comp (representedProduct A H ρ)

/-- The vector moment hypothesis identifies the bidual image of every
represented-vector map with the original vector. -/
theorem omega_representedVector
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (hmoment : ∀ ξ : H, omega (vectorMoment A H ρ ξ) = (‖ξ‖ ^ 2 : ℂ))
    (ξ : H) (g : StrongDual ℂ H) :
    omega (g.comp (representedVector A H ρ ξ)) = g ξ := by
  let η : H := (InnerProductSpace.toDual ℂ H).symm g
  have hg : g = innerSL ℂ η := by
    apply ContinuousLinearMap.ext
    intro v
    simpa [η] using (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (x := v) (y := g))
  rw [hg]
  exact omega_matrixCoefficient A H ρ omega hmoment η ξ

/-- A finite orthonormal basis gives a dimension-explicit operator-norm
bound after an orthogonal projection.  This includes the zero-dimensional
subspace. -/
theorem norm_comp_starProjection_le
    (U : Submodule ℂ H) [FiniteDimensional ℂ U]
    (S : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hS : ∀ i : Fin (Module.finrank ℂ U),
      ‖S ((stdOrthonormalBasis ℂ U i : U) : H)‖ ≤ δ) :
    ‖S.comp U.starProjection‖ ≤ (Module.finrank ℂ U : ℝ) * δ := by
  let e := stdOrthonormalBasis ℂ U
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hδ) fun v ↦ ?_
  have hP : U.starProjection v =
      ∑ i, inner ℂ ((e i : U) : H) v • ((e i : U) : H) := by
    change (U.orthogonalProjectionOnto v : H) = _
    simpa using congrArg Subtype.val (e.orthogonalProjectionOnto_apply_eq_sum v)
  rw [ContinuousLinearMap.comp_apply, hP, map_sum]
  simp_rw [map_smul]
  calc
    ‖∑ i, inner ℂ ((e i : U) : H) v • S ((e i : U) : H)‖ ≤
        ∑ i, ‖inner ℂ ((e i : U) : H) v • S ((e i : U) : H)‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖inner ℂ ((e i : U) : H) v‖ * ‖S ((e i : U) : H)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul]
    _ ≤ ∑ _i : Fin (Module.finrank ℂ U), ‖v‖ * δ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · calc
          ‖inner ℂ ((e i : U) : H) v‖ ≤ ‖((e i : U) : H)‖ * ‖v‖ :=
            norm_inner_le_norm _ _
          _ = ‖v‖ := by
            have hnorm : ‖((e i : U) : H)‖ = 1 := by
              change ‖e i‖ = 1
              exact e.norm_eq_one i
            rw [hnorm, one_mul]
      · exact hS i
      · exact norm_nonneg _
      · exact norm_nonneg _
    _ = ((Module.finrank ℂ U : ℝ) * δ) * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Fintype.card_fin]
      ring

/-- The finite family containing tensor-centrality constraints and the
represented action on an orthonormal basis of `U`. -/
def finiteConstraintMap
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (F : Finset A)
    (U : Submodule ℂ H) [FiniteDimensional ℂ U] :
    Tensor A →L[ℂ]
      ((F ⊕ Fin (Module.finrank ℂ U)) → (Tensor A × H)) :=
  ContinuousLinearMap.pi fun i ↦ match i with
    | .inl a => (leftAction ℂ A a.1 - rightAction ℂ A a.1).prod 0
    | .inr j => (0 : Tensor A →L[ℂ] Tensor A).prod
        (representedVector A H ρ ((stdOrthonormalBasis ℂ U j : U) : H))

/-- The target of `finiteConstraintMap`: zero centrality and identity action
on the finite-dimensional subspace. -/
def finiteConstraintTarget
    (F : Finset A) (U : Submodule ℂ H) [FiniteDimensional ℂ U] :
    (F ⊕ Fin (Module.finrank ℂ U)) → (Tensor A × H)
  | .inl _ => (0, 0)
  | .inr j => (0, ((stdOrthonormalBasis ℂ U j : U) : H))

/-- Conditional finite-rank row bridge.  The projection is the orthogonal
projection onto an arbitrary finite-dimensional subspace, including `⊥`.
The row is not asserted to satisfy a global identity in `A`. -/
theorem exists_finiteRow_approximate_on_subspace
    (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (omega : StrongDual ℂ (StrongDual ℂ (Tensor A)))
    (homega : InWeakStarClosure omega (rowConvexSet A))
    (hcentral : ∀ (a : A) (f : StrongDual ℂ (Tensor A)),
      omega (f.comp (leftAction ℂ A a)) =
        omega (f.comp (rightAction ℂ A a)))
    (hmoment : ∀ ξ : H, omega (vectorMoment A H ρ ξ) = (‖ξ‖ ^ 2 : ℂ))
    (F : Finset A) (U : Submodule ℂ H) [FiniteDimensional ℂ U]
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ (n : ℕ) (y : Fin n → A),
      (∑ i, ‖y i‖ ^ 2 ≤ 1) ∧
      0 ≤ rowSquare A y ∧ ‖rowSquare A y‖ ≤ 1 ∧
      ‖(ρ (rowSquare A y)).comp U.starProjection - U.starProjection‖ < τ ∧
      ∀ a ∈ F, ∀ b : A,
        ‖a * rowMap A y b - rowMap A y b * a‖ ≤ ε * ‖b‖ := by
  classical
  let d : ℝ := Module.finrank ℂ U
  let δ : ℝ := τ / (d + 1)
  have hd0 : 0 ≤ d := by simp [d]
  have hden : 0 < d + 1 := by linarith
  have hδ : 0 < δ := div_pos hτ hden
  let r : ℝ := min ε δ
  have hr : 0 < r := lt_min hε hδ
  let T := finiteConstraintMap A H ρ F U
  let z := finiteConstraintTarget A H F U
  have hcomponent : ∀ (i : F ⊕ Fin (Module.finrank ℂ U))
      (g : StrongDual ℂ (Tensor A × H)),
      omega (g.comp ((ContinuousLinearMap.proj i).comp T)) = g (z i) := by
    intro i g
    rcases i with a | j
    · let f : StrongDual ℂ (Tensor A) :=
        g.comp (ContinuousLinearMap.inl ℂ (Tensor A) H)
      have hcomp : g.comp ((ContinuousLinearMap.proj (Sum.inl a)).comp T) =
          f.comp (leftAction ℂ A a.1 - rightAction ℂ A a.1) := by
        apply ContinuousLinearMap.ext
        intro t
        rfl
      have hsub : f.comp (leftAction ℂ A a.1 - rightAction ℂ A a.1) =
          f.comp (leftAction ℂ A a.1) - f.comp (rightAction ℂ A a.1) := by
        apply ContinuousLinearMap.ext
        intro t
        exact map_sub f _ _
      rw [hcomp, hsub, map_sub, hcentral, sub_self]
      change (0 : ℂ) = g 0
      exact (map_zero g).symm
    · let gH : StrongDual ℂ H :=
        g.comp (ContinuousLinearMap.inr ℂ (Tensor A) H)
      let e : H := ((stdOrthonormalBasis ℂ U j : U) : H)
      have hcomp : g.comp ((ContinuousLinearMap.proj (Sum.inr j)).comp T) =
          gH.comp (representedVector A H ρ e) := by
        apply ContinuousLinearMap.ext
        intro t
        rfl
      rw [hcomp, omega_representedVector A H ρ omega hmoment e gH]
      rfl
  let M : Tensor A →L[ℂ] (Fin 0 → ℂ) := 0
  obtain ⟨t, htD, ht, -⟩ :=
    exists_finite_norm_and_moment_lt_of_components
      (X := Tensor A) (Z := Tensor A × H)
      (ι := F ⊕ Fin (Module.finrank ℂ U)) (κ := Fin 0)
      (convex_rowConvexSet A) homega T M z (fun e ↦ nomatch e)
      hcomponent (fun e ↦ nomatch e) hr
  obtain ⟨n, y, hyt, hybudget⟩ := exists_row_of_mem_rowConvexSet A htD
  refine ⟨n, y, hybudget, rowSquare_nonneg A y,
    (norm_rowSquare_le_budget A y).trans hybudget, ?_, ?_⟩
  · let S : H →L[ℂ] H := representationCLM A H ρ (rowSquare A y) -
      ContinuousLinearMap.id ℂ H
    have hSy : ∀ j : Fin (Module.finrank ℂ U),
        ‖S ((stdOrthonormalBasis ℂ U j : U) : H)‖ ≤ r := by
      intro j
      have hj := ht (Sum.inr j)
      change ‖(0, representedVector A H ρ
        ((stdOrthonormalBasis ℂ U j : U) : H) t) -
          (0, ((stdOrthonormalBasis ℂ U j : U) : H))‖ < r at hj
      have hj' : ‖representedVector A H ρ
          ((stdOrthonormalBasis ℂ U j : U) : H) t -
          ((stdOrthonormalBasis ℂ U j : U) : H)‖ < r := by
        simpa using hj
      change ‖ρ (rowSquare A y) ((stdOrthonormalBasis ℂ U j : U) : H) -
          ((stdOrthonormalBasis ℂ U j : U) : H)‖ ≤ r
      rw [← multiplication_rowTensor A y, hyt]
      exact hj'.le
    have hSr : ‖S.comp U.starProjection‖ ≤
        (Module.finrank ℂ U : ℝ) * r :=
      norm_comp_starProjection_le H U S hr.le hSy
    have hrδ : r ≤ δ := min_le_right _ _
    have hdδ : (Module.finrank ℂ U : ℝ) * r ≤ d * δ := by
      change d * r ≤ d * δ
      exact mul_le_mul_of_nonneg_left hrδ hd0
    have hdτ : d * δ < τ := by
      calc
        d * δ = τ * (d / (d + 1)) := by
          dsimp [δ]
          field_simp
          <;> ring
        _ < τ * 1 := mul_lt_mul_of_pos_left ((div_lt_one hden).2 (by linarith)) hτ
        _ = τ := mul_one _
    have heq : (ρ (rowSquare A y)).comp U.starProjection - U.starProjection =
        S.comp U.starProjection := by
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq]
    exact hSr.trans_lt (hdδ.trans_lt hdτ)
  · intro a ha b
    let ia : F := ⟨a, ha⟩
    have haT := ht (Sum.inl ia)
    change ‖(leftAction ℂ A a t - rightAction ℂ A a t, 0) - (0, 0)‖ < r at haT
    have haT' : ‖leftAction ℂ A a (rowTensor A y) -
        rightAction ℂ A a (rowTensor A y)‖ < ε := by
      rw [hyt]
      have haTr : ‖leftAction ℂ A a t - rightAction ℂ A a t‖ < r := by
        simpa using haT
      exact haTr.trans_le (min_le_left _ _)
    calc
      ‖a * rowMap A y b - rowMap A y b * a‖ = ‖rowCommutator A a y b‖ := rfl
      _ ≤ ‖rowCommutator A a y‖ * ‖b‖ := (rowCommutator A a y).le_opNorm b
      _ ≤ ε * ‖b‖ := mul_le_mul_of_nonneg_right
        ((norm_rowCommutator_le_tensor A a y).trans haT'.le) (norm_nonneg b)

end

end MathlibAnnex.CStarAlgebra.TensorAveraging
