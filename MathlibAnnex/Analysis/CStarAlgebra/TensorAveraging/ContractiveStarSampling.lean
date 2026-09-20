import MathlibAnnex.Analysis.CStarAlgebra.TwoSidedInterpolation
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.VectorDomination

/-!
# A norm-controlled source net with simultaneous strong-star convergence

For each finite set of vectors choose the *single* sharp Kadison witness for
both `T` and `T*`.  The resulting net is eventually exactly correct on each
fixed vector.  This removes the old self-adjoint restriction without changing
the norm budget.  It does not assert operator-norm convergence, arbitrary
normal-functional continuity, or the existence of an invariant mean.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped InnerProduct CStarAlgebra
open MathlibAnnex.Analysis.CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.TensorAveraging

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Choice is made once for both adjoint directions at each finite set. -/
def contractiveStarSample
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (s : Finset H) : A :=
  Classical.choose (exists_norm_le_and_both_eq_finset pi hpi s T)

theorem contractiveStarSample_spec
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (s : Finset H) :
    ‖contractiveStarSample pi hpi T s‖ ≤ ‖T‖ ∧
      (∀ x ∈ s, pi (contractiveStarSample pi hpi T s) x = T x) ∧
      (∀ x ∈ s, pi (star (contractiveStarSample pi hpi T s)) x = (star T) x) :=
  Classical.choose_spec (exists_norm_le_and_both_eq_finset pi hpi s T)

/-- Every fixed vector is eventually interpolated exactly, in both directions. -/
theorem contractiveStarSample_eventually_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (x : H) :
    ∀ᶠ s : Finset H in atTop,
      pi (contractiveStarSample pi hpi T s) x = T x ∧
      pi (star (contractiveStarSample pi hpi T s)) x = (star T) x := by
  classical
  filter_upwards [eventually_ge_atTop ({x} : Finset H)] with s hs
  have hx : x ∈ s := hs (Finset.mem_singleton_self x)
  exact ⟨(contractiveStarSample_spec pi hpi T s).2.1 x hx,
    (contractiveStarSample_spec pi hpi T s).2.2 x hx⟩

/-- The actual represented sample net, with its sharp bound and both strong
limits.  No strong-star density supplier is passed as an argument. -/
theorem contractiveStarSample_strongStar
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) :
    (∀ s, ‖contractiveStarSample pi hpi T s‖ ≤ ‖T‖) ∧
    ContinuousLinearMap.StronglyConverges
      (fun s => pi (contractiveStarSample pi hpi T s)) atTop T ∧
    ContinuousLinearMap.StronglyConverges
      (fun s => star (pi (contractiveStarSample pi hpi T s))) atTop (star T) := by
  refine ⟨fun s => (contractiveStarSample_spec pi hpi T s).1, ?_, ?_⟩
  · intro x
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [contractiveStarSample_eventually_eq pi hpi T x] with s hs
    exact hs.1.symm
  · intro x
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [contractiveStarSample_eventually_eq pi hpi T x] with s hs
    simpa only [map_star] using hs.2.symm

/-- An actual source net for every contraction, including proper isometries.
The source elements are contractions, not falsely claimed to be unitaries. -/
theorem exists_contracting_strongStar_source_net
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ a : Finset H → A, (∀ s, ‖a s‖ ≤ 1) ∧
      ContinuousLinearMap.StronglyConverges (fun s => pi (a s)) atTop T ∧
      ContinuousLinearMap.StronglyConverges (fun s => star (pi (a s))) atTop
        (star T) := by
  obtain ⟨hb, hf, hs⟩ := contractiveStarSample_strongStar pi hpi T
  exact ⟨contractiveStarSample pi hpi T, fun s => (hb s).trans hT, hf, hs⟩

/-- All concrete vector gauges converge along this same net. -/
theorem tendsto_contractiveStarSample_vectorGauge_zero
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) (xi : H) :
    Tendsto (fun s => MathlibAnnex.CStarBilinear.strongStarGauge
      (operatorVectorState H xi) (pi (contractiveStarSample pi hpi T s) - T))
      atTop (𝓝 0) := by
  obtain ⟨_, hf, hs⟩ := contractiveStarSample_strongStar pi hpi T
  exact tendsto_strongStarGauge_zero H _ T hf hs xi

/-- A finite family of concrete vector gauges can in fact vanish exactly on
one source witness; no epsilon budget is consumed by this step. -/
theorem exists_contraction_finite_vectorGauge_eq_zero
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] (xi : I → H)
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ i,
      MathlibAnnex.CStarBilinear.strongStarGauge
        (operatorVectorState H (xi i)) (pi a - T) = 0 := by
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_family pi hpi xi T
  refine ⟨a, ha.trans hT, ?_⟩
  intro i
  rw [strongStarGauge_operatorVectorState]
  have hstar : (star (pi a - T)) (xi i) = 0 := by
    rw [star_sub, ← map_star, ContinuousLinearMap.sub_apply, hs i, sub_self]
  simp only [ContinuousLinearMap.sub_apply, hf i, sub_self,
    hstar, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_zero]

/-- A finite family of product matrix coefficients shares the same witness.
There is no assertion about arbitrary projective-tensor dual functionals. -/
theorem exists_contraction_finite_matrixProduct_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    {I : Type*} [Fintype I] (eta xi : I → H)
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    ∃ a : A, ‖a‖ ≤ 1 ∧ ∀ i,
      operatorMatrixCoefficient H (eta i) (xi i) (pi a * pi a) =
      operatorMatrixCoefficient H (eta i) (xi i) (T * T) := by
  classical
  let zeta : Sum I I → H := Sum.elim eta xi
  obtain ⟨a, ha, hf, hs⟩ := exists_norm_le_and_both_eq_family pi hpi zeta T
  refine ⟨a, ha.trans hT, ?_⟩
  intro i
  have hxi : pi a (xi i) = T (xi i) := by
    simpa [zeta] using hf (Sum.inr i)
  have heta : (star (pi a)) (eta i) = (star T) (eta i) := by
    simpa [zeta, map_star] using hs (Sum.inl i)
  change inner ℂ (eta i) ((pi a * pi a) (xi i)) =
    inner ℂ (eta i) ((T * T) (xi i))
  simp only [ContinuousLinearMap.mul_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left (pi a),
    ← ContinuousLinearMap.adjoint_inner_left T]
  simpa only [← ContinuousLinearMap.star_eq_adjoint, heta, hxi]

end MathlibAnnex.CStarAlgebra.TensorAveraging
