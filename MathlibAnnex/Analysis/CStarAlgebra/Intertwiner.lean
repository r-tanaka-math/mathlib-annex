import Mathlib.Analysis.Normed.Operator.Banach
import MathlibAnnex.Analysis.CStarAlgebra.Schur

/-!
# Bounded intertwiners of irreducible star representations

The adjoint of an intertwiner intertwines in the reverse direction.  Thus its
initial positive operator lies in the commutant.  The arbitrary-dimensional
Schur theorem makes that operator scalar; after positive normalization, the
intertwiner is an isometry.  Its closed range reduces the target
representation, so target irreducibility makes it onto.
-/

set_option autoImplicit false

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The closed linear range of a bounded linear map. -/
noncomputable def rangeClosure (T : E →L[𝕜] F) : Submodule 𝕜 F :=
  (LinearMap.range T.toLinearMap).topologicalClosure

theorem isClosed_rangeClosure (T : E →L[𝕜] F) :
    IsClosed (T.rangeClosure : Set F) :=
  (LinearMap.range T.toLinearMap).isClosed_topologicalClosure

theorem range_le_rangeClosure (T : E →L[𝕜] F) :
    LinearMap.range T.toLinearMap ≤ T.rangeClosure :=
  (LinearMap.range T.toLinearMap).le_topologicalClosure

end ContinuousLinearMap

namespace StarAlgHom

variable {A H K : Type*}
variable [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded operator intertwines two star representations. -/
def Intertwines (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K) : Prop :=
  ∀ a, V.comp (π a) = (σ a).comp V

/-- Taking adjoints reverses a bounded intertwiner. -/
theorem Intertwines.adjoint
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    {V : H →L[ℂ] K} (hV : Intertwines π σ V) :
    Intertwines σ π (ContinuousLinearMap.adjoint V) := by
  intro a
  have h := congrArg ContinuousLinearMap.adjoint (hV (star a))
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp] at h
  have hπ : ContinuousLinearMap.adjoint (π (star a)) = π a := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star, star_star]
  have hσ : ContinuousLinearMap.adjoint (σ (star a)) = σ a := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star, star_star]
  rw [hπ, hσ] at h
  exact h.symm

/-- The positive initial operator of an intertwiner is in the source
commutant. -/
theorem Intertwines.adjoint_comp_self_inCommutant
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    {V : H →L[ℂ] K} (hV : Intertwines π σ V) :
    InCommutant π ((ContinuousLinearMap.adjoint V).comp V) := by
  have hVa := hV.adjoint
  intro a
  change ((ContinuousLinearMap.adjoint V).comp V).comp (π a) =
    (π a).comp ((ContinuousLinearMap.adjoint V).comp V)
  calc
    ((ContinuousLinearMap.adjoint V).comp V).comp (π a) =
        (ContinuousLinearMap.adjoint V).comp (V.comp (π a)) :=
      ContinuousLinearMap.comp_assoc _ _ _
    _ = (ContinuousLinearMap.adjoint V).comp ((σ a).comp V) := by rw [hV a]
    _ = ((ContinuousLinearMap.adjoint V).comp (σ a)).comp V :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = ((π a).comp (ContinuousLinearMap.adjoint V)).comp V := by rw [hVa a]
    _ = (π a).comp ((ContinuousLinearMap.adjoint V).comp V) :=
      ContinuousLinearMap.comp_assoc _ _ _

/-- The closed range of an intertwiner reduces the target representation. -/
theorem Intertwines.rangeClosure_isReducing
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    {V : H →L[ℂ] K} (hV : Intertwines π σ V) :
    IsReducing σ V.rangeClosure := by
  have hinv (a : A) : V.rangeClosure.IsInvariantUnder (σ a) := by
    intro x hx
    change x ∈ closure (LinearMap.range V.toLinearMap) at hx
    change σ a x ∈ closure (LinearMap.range V.toLinearMap)
    apply (show Set.MapsTo (σ a) (LinearMap.range V.toLinearMap)
        (LinearMap.range V.toLinearMap) by
      rintro _ ⟨y, rfl⟩
      refine ⟨π a y, ?_⟩
      change V (π a y) = σ a (V y)
      have ha := congrArg (fun T : H →L[ℂ] K ↦ T y) (hV a)
      change V (π a y) = σ a (V y) at ha
      exact ha).closure (σ a).continuous hx
  intro a
  refine ⟨hinv a, ?_⟩
  have hadj : σ (star a) = ContinuousLinearMap.adjoint (σ a) := by
    rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  rw [← hadj]
  exact hinv (star a)

private theorem rangeClosure_ne_bot {V : H →L[ℂ] K} (hV : V ≠ 0) :
    V.rangeClosure ≠ ⊥ := by
  intro hbot
  apply hV
  ext x
  have hx : V x ∈ V.rangeClosure :=
    V.range_le_rangeClosure (LinearMap.mem_range_self V.toLinearMap x)
  rw [hbot, Submodule.mem_bot] at hx
  exact hx

private theorem rangeClosure_eq_top_of_irreducible
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    (hσ : IsIrreducible σ) {V : H →L[ℂ] K} (hV : V ≠ 0)
    (hint : Intertwines π σ V) : V.rangeClosure = ⊤ := by
  rcases hσ V.rangeClosure V.isClosed_rangeClosure
      hint.rangeClosure_isReducing with hbot | htop
  · exact (rangeClosure_ne_bot hV hbot).elim
  · exact htop

/-- A nonzero bounded intertwiner between irreducible complex star
representations is a positive real multiple of a unitary intertwiner.  This
uses no finite-dimensional hypothesis. -/
theorem Intertwines.eq_zero_or_smul_unitary [Nontrivial H] [Nontrivial K]
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    (hπ : IsIrreducible π) (hσ : IsIrreducible σ)
    {V : H →L[ℂ] K} (hV : Intertwines π σ V) :
    V = 0 ∨ ∃ c : ℝ, 0 < c ∧ ∃ U : H ≃ₗᵢ[ℂ] K,
      Intertwines π σ (U : H →L[ℂ] K) ∧
        V = (c : ℂ) • (U : H →L[ℂ] K) := by
  by_cases hVzero : V = 0
  · exact Or.inl hVzero
  right
  have hPself : IsSelfAdjoint ((ContinuousLinearMap.adjoint V).comp V) := by
    rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨r, hr⟩ := eq_algebraMap_of_isSelfAdjoint_of_irreducible
    π hπ ((ContinuousLinearMap.adjoint V).comp V) hPself
      hV.adjoint_comp_self_inCommutant
  have hnormsq (x : H) : ‖V x‖ ^ 2 = r * ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left, hr,
      ContinuousLinearMap.algebraMap_apply]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left,
      RCLike.smul_re]
    rw [← InnerProductSpace.norm_sq_eq_re_inner]
  obtain ⟨x, hx⟩ : ∃ x, V x ≠ 0 := by
    by_contra h
    apply hVzero
    ext y
    by_contra hy
    exact h ⟨y, hy⟩
  have hxzero : x ≠ 0 := by
    intro h
    subst x
    simp at hx
  have hrpos : 0 < r := by
    have hVnormpos : 0 < ‖V x‖ := norm_pos_iff.mpr hx
    have hxnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hxzero
    have heq := hnormsq x
    nlinarith [sq_pos_of_pos hVnormpos, sq_pos_of_pos hxnormpos]
  let c : ℝ := √r
  have hcpos : 0 < c := Real.sqrt_pos.2 hrpos
  have hcsq : c ^ 2 = r := by
    simpa [c] using Real.sq_sqrt hrpos.le
  have hVnorm (y : H) : ‖V y‖ = c * ‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hcpos.le (norm_nonneg _))).mp
    rw [hnormsq, mul_pow, hcsq]
  let W : H →L[ℂ] K := (c⁻¹ : ℂ) • V
  have hWisometry : Isometry W := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro y
    rw [smul_apply, norm_smul, hVnorm, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hcpos]
    field_simp
  have hWintertwines : Intertwines π σ W := by
    intro a
    apply ContinuousLinearMap.ext
    intro y
    have hy := congrArg (fun T : H →L[ℂ] K ↦ T y) (hV a)
    change V (π a y) = σ a (V y) at hy
    simp [W, ContinuousLinearMap.comp_apply, hy]
  have hWzero : W ≠ 0 := by
    intro hW
    apply hVzero
    ext y
    have hy := congrArg (fun T : H →L[ℂ] K ↦ T y) hW
    change (c⁻¹ : ℂ) • V y = 0 at hy
    exact (smul_eq_zero.mp hy).resolve_left
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hcpos.ne'))
  have hWtop : W.rangeClosure = ⊤ :=
    rangeClosure_eq_top_of_irreducible hσ hWzero hWintertwines
  have hWsurjective : Function.Surjective W := by
    intro y
    have hy : y ∈ (W.rangeClosure : Set K) := by
      rw [hWtop]
      exact Submodule.mem_top
    change y ∈ closure (Set.range W) at hy
    rw [hWisometry.isClosedEmbedding.isClosed_range.closure_eq] at hy
    exact hy
  let w : H →ₗᵢ[ℂ] K := W.toLinearMap.toLinearIsometry hWisometry
  have hwsurjective : Function.Surjective w := by
    intro y
    obtain ⟨x, hx⟩ := hWsurjective y
    exact ⟨x, hx⟩
  let U : H ≃ₗᵢ[ℂ] K := LinearIsometryEquiv.ofSurjective w hwsurjective
  have hUapply (y : H) : U y = W y := by
    rfl
  refine ⟨c, hcpos, U, ?_, ?_⟩
  · intro a
    apply ContinuousLinearMap.ext
    intro y
    change U (π a y) = σ a (U y)
    rw [hUapply, hUapply]
    have hy := congrArg (fun T : H →L[ℂ] K ↦ T y) (hWintertwines a)
    simpa [ContinuousLinearMap.comp_apply] using hy
  · apply ContinuousLinearMap.ext
    intro y
    change V y = (c : ℂ) • U y
    rw [hUapply]
    change V y = (c : ℂ) • ((c⁻¹ : ℂ) • V y)
    simp [smul_smul, hcpos.ne']

/-- If no unitary intertwiner exists between two irreducible
representations, every bounded intertwiner between them is zero. -/
theorem Intertwines.eq_zero_of_no_unitary [Nontrivial H] [Nontrivial K]
    {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)}
    (hπ : IsIrreducible π) (hσ : IsIrreducible σ)
    (hno : ∀ U : H ≃ₗᵢ[ℂ] K,
      ¬ Intertwines π σ (U : H →L[ℂ] K))
    {V : H →L[ℂ] K} (hV : Intertwines π σ V) : V = 0 := by
  rcases hV.eq_zero_or_smul_unitary hπ hσ with hzero | ⟨_, _, U, hU, _⟩
  · exact hzero
  · exact (hno U hU).elim

end StarAlgHom
