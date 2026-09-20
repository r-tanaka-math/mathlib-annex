import MathlibAnnex.Analysis.CStarAlgebra.AsymptoticallyInner
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Restricting start-at-one asymptotic innerness to a nonunital algebra

C05 controller-authored source, UNBUILT. The scalar quotient is fixed by
every inner conjugation, hence by its point-norm limit. Both alpha and its
inverse preserve the ORIGINAL ideal in the unitization. The same U and
alpha supply the restriction, not independently chosen witnesses.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace MathlibAnnex.CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The unitary path lives in the minimal unitization. This definition does
not require a unit in A and does not claim point-norm convergence of U itself. -/
def IsAsymptoticallyInnerFromOneNonUnital (beta : A ≃⋆ₐ[ℂ] A) : Prop :=
  ∃ U : ℝ → unitary (Unitization ℂ A), Continuous U ∧ U 0 = 1 ∧
    ∀ a : A, Tendsto
      (fun t => Unitary.conjStarAlgAut ℂ (Unitization ℂ A) (U t) (Unitization.inr a))
      atTop (𝓝 (Unitization.inr (beta a)))

/-- Central scalar phases disappear under conjugation. -/
theorem unitization_fst_conjugate (u : unitary (Unitization ℂ A))
    (z : Unitization ℂ A) :
    (Unitary.conjStarAlgAut ℂ (Unitization ℂ A) u z).fst = z.fst := by
  have hu : (u : Unitization ℂ A).fst * star (u : Unitization ℂ A).fst = 1 :=
    congrArg (fun w : Unitization ℂ A => w.fst) u.property.2
  change (u : Unitization ℂ A).fst * z.fst * star (u : Unitization ℂ A).fst = z.fst
  calc
    _ = z.fst * ((u : Unitization ℂ A).fst * star (u : Unitization ℂ A).fst) := by ring
    _ = z.fst := by rw [hu, mul_one]

/-- Forward preservation of the scalar quotient follows from the actual
asymptotic path. It is not an extra ideal-invariance hypothesis. -/
theorem IsAsymptoticallyInnerFromOne.unitization_fst
    {alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A}
    (h : IsAsymptoticallyInnerFromOne alpha) (z : Unitization ℂ A) :
    (alpha z).fst = z.fst := by
  obtain ⟨U, hU, hU0, hlim⟩ := h
  have ht := (Unitization.continuous_fst.tendsto _).comp (hlim z)
  apply tendsto_nhds_unique ht
  exact tendsto_const_nhds.congr'
    (Eventually.of_forall fun t => (unitization_fst_conjugate (U t) z).symm)

private theorem unitization_inr_snd (z : Unitization ℂ A) (hz : z.fst = 0) :
    Unitization.inr z.snd = z := by
  exact Unitization.ext (by simpa using hz.symm) rfl

private theorem inverse_preserves_fst
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (hfst : ∀ z, (alpha z).fst = z.fst) (z : Unitization ℂ A) :
    (alpha.symm z).fst = z.fst := by
  simpa only [alpha.apply_symm_apply] using (hfst (alpha.symm z)).symm

private noncomputable def unitizationRestrictHom
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (hfst : ∀ z, (alpha z).fst = z.fst) : A →⋆ₙₐ[ℂ] A where
  toFun a := (alpha (Unitization.inr a)).snd
  map_zero' := by simp
  map_add' a b := by
    simpa using congrArg (fun z : Unitization ℂ A => z.snd)
      (map_add alpha (Unitization.inr a) (Unitization.inr b))
  map_smul' c a := by
    simpa using congrArg (fun z : Unitization ℂ A => z.snd)
      (map_smul alpha c (Unitization.inr a))
  map_star' a := by
    simpa using congrArg (fun z : Unitization ℂ A => z.snd)
      (map_star alpha (Unitization.inr a))
  map_mul' a b := by
    have ha := unitization_inr_snd (alpha (Unitization.inr a)) (by simp [hfst])
    have hb := unitization_inr_snd (alpha (Unitization.inr b)) (by simp [hfst])
    have h := congrArg (fun z : Unitization ℂ A => z.snd)
      (map_mul alpha (Unitization.inr a) (Unitization.inr b))
    rw [← ha, ← hb] at h
    simpa using h

private theorem unitization_restrictHom_inr
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (hfst : ∀ z, (alpha z).fst = z.fst) (a : A) :
    Unitization.inr (unitizationRestrictHom alpha hfst a) =
      alpha (Unitization.inr a) :=
  unitization_inr_snd _ (by simp [hfst])

/-- Restriction includes the inverse and all algebra operations. The input
is ordinary scalar-quotient preservation, subsequently proved from a path. -/
noncomputable def unitizationRestrictEquiv
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (hfst : ∀ z, (alpha z).fst = z.fst) : A ≃⋆ₐ[ℂ] A := by
  let f := unitizationRestrictHom alpha hfst
  let g := unitizationRestrictHom alpha.symm (inverse_preserves_fst alpha hfst)
  refine StarAlgEquiv.ofNonUnitalStarAlgHom f g ?_ ?_
  · ext a
    apply Unitization.inr_injective (R := ℂ)
    change Unitization.inr (g (f a)) = Unitization.inr a
    rw [unitization_restrictHom_inr, unitization_restrictHom_inr,
      alpha.symm_apply_apply]
  · ext a
    apply Unitization.inr_injective (R := ℂ)
    change Unitization.inr (f (g a)) = Unitization.inr a
    rw [unitization_restrictHom_inr, unitization_restrictHom_inr,
      alpha.apply_symm_apply]

@[simp]
theorem unitizationRestrictEquiv_inr
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (hfst : ∀ z, (alpha z).fst = z.fst) (a : A) :
    Unitization.inr (unitizationRestrictEquiv alpha hfst a) =
      alpha (Unitization.inr a) :=
  unitization_restrictHom_inr alpha hfst a

/-- Asymptotic innerness of the restriction is witnessed by the SAME path. -/
theorem IsAsymptoticallyInnerFromOne.restrict_nonUnital
    {alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A}
    (h : IsAsymptoticallyInnerFromOne alpha) :
    IsAsymptoticallyInnerFromOneNonUnital
      (unitizationRestrictEquiv alpha h.unitization_fst) := by
  obtain ⟨U, hU, hU0, hlim⟩ := h
  refine ⟨U, hU, hU0, ?_⟩
  intro a
  simpa only [unitizationRestrictEquiv_inr] using hlim (Unitization.inr a)

/-- The inverse actions also converge in the original algebra, with the
same U; no second unrelated asymptotic witness is introduced. -/
theorem unitization_restriction_twoSided_path
    (alpha : Unitization ℂ A ≃⋆ₐ[ℂ] Unitization ℂ A)
    (U : ℝ → unitary (Unitization ℂ A))
    (hU : Continuous U) (hU0 : U 0 = 1)
    (hlim : ∀ z, Tendsto
      (fun t => Unitary.conjStarAlgAut ℂ (Unitization ℂ A) (U t) z)
      atTop (𝓝 (alpha z))) :
    ∃ beta : A ≃⋆ₐ[ℂ] A,
      (∀ a, Unitization.inr (beta a) = alpha (Unitization.inr a)) ∧
      (∀ a, Tendsto
        (fun t => (Unitary.conjStarAlgAut ℂ (Unitization ℂ A) (U t)
          (Unitization.inr a)).snd) atTop (𝓝 (beta a))) ∧
      (∀ a, Tendsto
        (fun t => ((Unitary.conjStarAlgAut ℂ (Unitization ℂ A) (U t)).symm
          (Unitization.inr a)).snd) atTop (𝓝 (beta.symm a))) := by
  let h : IsAsymptoticallyInnerFromOne alpha := ⟨U, hU, hU0, hlim⟩
  let beta := unitizationRestrictEquiv alpha h.unitization_fst
  refine ⟨beta, unitizationRestrictEquiv_inr alpha h.unitization_fst, ?_, ?_⟩
  · intro a
    exact (Unitization.continuous_snd.tendsto _).comp (hlim (Unitization.inr a))
  · intro a
    have ht := tendsto_symm_apply_atTop_of_tendsto
      (fun t => Unitary.conjStarAlgAut ℂ (Unitization ℂ A) (U t)) alpha hlim
      (Unitization.inr a)
    exact (Unitization.continuous_snd.tendsto _).comp ht

end MathlibAnnex.CStarAlgebra
