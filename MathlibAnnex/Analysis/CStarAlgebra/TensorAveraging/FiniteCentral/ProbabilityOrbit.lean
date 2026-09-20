import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteGroupBalance
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.FiniteCentral.CornerSpan

/-!
# An actual normalized finite isometry average

C06, UNBUILT. The cardinal normalization is done once and is independent of
test size and of matrix dimension. Range projections remain identical for
all orbit points wU(g); source isometries are not claimed to be unitaries.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
open scoped BigOperators CStarAlgebra
namespace MathlibAnnex.FiniteCentral
open MathlibAnnex.CStarAlgebra.TensorAveraging
universe u v
variable {M : Type u} [CStarAlgebra M] [Nontrivial M]
variable {G : Type v} [Group G] [Fintype G]

/-- All coefficients are the same nonnegative REAL number. -/
def uniformOrbit (U : G → M) (hU : ∀ g, star (U g) * U g = 1)
    (w : M) (hw : star w * w = 1) : FiniteIsometryAverage M where
  size := Fintype.card G
  point := fun i => ⟨w * U ((Fintype.equivFin G).symm i),
    orbit_isometry U hU w hw _⟩
  weight := fun _ => (Fintype.card G : ℝ)⁻¹
  weight_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  weight_sum := by
    have hn : (Fintype.card G : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

theorem uniformOrbit_value (U : G → M) (hU : ∀ g, star (U g) * U g = 1)
    (w : M) (hw : star w * w = 1) (B : ContinuousBilinearForm M) :
    (uniformOrbit U hU w hw).value B = (Fintype.card G : ℂ)⁻¹ * orbitSum U w B := by
  classical
  simp only [uniformOrbit, FiniteIsometryAverage.value, ← Finset.mul_sum]
  have hs := Equiv.sum_comp (Fintype.equivFin G).symm
    (fun g => B (star (w * U g)) (w * U g))
  convert congrArg (fun z : ℂ => (Fintype.card G : ℂ)⁻¹ * z) hs using 1
    <;> simp [orbitSum, Complex.ofReal_inv, Complex.ofReal_natCast] <;> congr 1

/-- Exact balance is AFTER averaging and extends over the full group span. -/
theorem uniformOrbit_defect_eq_zero (U : G → M)
    (hU : ∀ g, star (U g) * U g = 1)
    (hU' : ∀ g, U g * star (U g) = 1)
    (hmul : ∀ g h, U (g*h) = U g * U h)
    (w : M) (hw : star w * w = 1) (B : ContinuousBilinearForm M) (a : M)
    (ha : a ∈ Submodule.span ℂ (Set.range U)) :
    (uniformOrbit U hU w hw).defect a B = 0 := by
  rw [FiniteIsometryAverage.defect, uniformOrbit_value, uniformOrbit_value,
    orbitSum_balance_span U hmul hU' w B a ha, sub_self]

theorem uniformOrbit_range (U : G → M)
    (hU : ∀ g, star (U g) * U g = 1)
    (hU' : ∀ g, U g * star (U g) = 1)
    (w : M) (hw : star w * w = 1)
    (i : Fin (uniformOrbit U hU w hw).size) :
    ((uniformOrbit U hU w hw).point i).val *
        star (((uniformOrbit U hU w hw).point i).val) = w * star w :=
  orbit_range_projection U hU' w _

end MathlibAnnex.FiniteCentral
