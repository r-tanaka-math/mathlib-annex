import MathlibAnnex.Analysis.CStarAlgebra.State.GNSKernel
import MathlibAnnex.Analysis.CStarAlgebra.State.NonUnitalApproximation

/-!
# The actual nonunital GNS kernel and canonical unitization

C05 controller source, UNBUILT. Kernels refer to Mathlib's
`gnsNonUnitalStarAlgHom`, not to the scalar functional nullspace. Equal
nonunital GNS kernels imply equal canonical unitization GNS kernels.
No assertion that a primitive quotient is simple is made.
-/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ComplexOrder InnerProduct Topology
namespace MathlibAnnex.Analysis.CStarAlgebra
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def nonUnitalStateGNSKernel (phi : A →L[ℂ] ℂ) : Set A :=
  {a | ∀ b : A, phi (star (a * b) * (a * b)) = 0}

noncomputable def nonUnitalStatePositiveMap
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ phi.toLinearMap hphi.1

private theorem nonUnital_gns_apply_toPreGNS
    (f : A →ₚ[ℂ] ℂ) (a b : A) :
    f.gnsNonUnitalStarAlgHom a (f.toPreGNS b : f.GNS) =
      (f.toPreGNS (a * b) : f.GNS) := by
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

private theorem nonUnital_gns_inner_toPreGNS
    (f : A →ₚ[ℂ] ℂ) (b : A) :
    inner ℂ (f.toPreGNS b : f.GNS) (f.toPreGNS b : f.GNS) = f (star b * b) := by
  rw [UniformSpace.Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  rfl

/-- Intrinsic criterion for the actual (not unitized) Mathlib GNS kernel. -/
theorem mem_nonUnitalStateGNSKernel_iff
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A) (a : A) :
    a ∈ nonUnitalStateGNSKernel phi ↔
      (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom a = 0 := by
  let f := nonUnitalStatePositiveMap phi hphi
  have hdense : DenseRange (fun b : A => (f.toPreGNS b : f.GNS)) :=
    UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe f.PreGNS)
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro y
    exact hdense.induction_on y
      (isClosed_eq (f.gnsNonUnitalStarAlgHom a).continuous continuous_const) fun b => by
        rw [nonUnital_gns_apply_toPreGNS]
        apply (inner_self_eq_zero (𝕜 := ℂ)).mp
        rw [nonUnital_gns_inner_toPreGNS]
        exact h b
  · intro h b
    have hz : (f.toPreGNS (a * b) : f.GNS) = 0 := by
      rw [← nonUnital_gns_apply_toPreGNS, h]
      simp
    change f (star (a * b) * (a * b)) = 0
    rw [← nonUnital_gns_inner_toPreGNS, hz]
    simp

/-- A state vanishes on its GNS kernel also without an algebra unit. The
approximate unit is used twice, with its norm limit explicitly retained. -/
theorem nonUnitalState_eq_zero_of_gns_eq_zero
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A) {a : A}
    (ha : (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom a = 0) :
    phi a = 0 := by
  have hker := (mem_nonUnitalStateGNSKernel_iff phi hphi a).2 ha
  have hmul := (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left a
  have hsquare : Tendsto (fun e : A => phi (star (a * e) * (a * e)))
      (CStarAlgebra.approximateUnit A) (𝓝 (phi (star a * a))) :=
    (phi.continuous.tendsto _).comp (hmul.star.mul hmul)
  have hsqzero : phi (star a * a) = 0 :=
    tendsto_nhds_unique hsquare
      (tendsto_const_nhds.congr' (Eventually.of_forall fun e => (hker e).symm))
  have hcross (e : A) : phi (star e * a) = 0 := by
    have h := norm_apply_star_mul_le phi hphi.1 e a
    rw [hsqzero] at h
    simp only [Complex.zero_re, Real.sqrt_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hleft := (CStarAlgebra.increasingApproximateUnit A).tendsto_mul_right a
  have ht : Tendsto (fun e : A => phi (e * a))
      (CStarAlgebra.approximateUnit A) (𝓝 (phi a)) :=
    (phi.continuous.tendsto _).comp hleft
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [(CStarAlgebra.increasingApproximateUnit A).eventually_nonneg]
    with e he
  simpa [he.isSelfAdjoint.star_eq] using (hcross e).symm

private theorem unitized_gns_apply_toPreGNS
    (f : A →ₚ[ℂ] ℂ) (z : Unitization ℂ A) (b : A) :
    (NonUnitalCStarRepresentation.unitization f.gnsNonUnitalStarAlgHom) z
        (f.toPreGNS b : f.GNS) =
      (f.toPreGNS (z.fst • b + z.snd * b) : f.GNS) := by
  induction z using Unitization.ind with
  | inl_add_inr c a =>
    simp [NonUnitalCStarRepresentation.unitization, nonUnital_gns_apply_toPreGNS,
      map_add, map_smul, UniformSpace.Completion.coe_add,
      UniformSpace.Completion.coe_smul]

/-- A zero operator in the canonical extended state's GNS also vanishes
in the unitization of the original GNS, tested on the dense pre-GNS image. -/
private theorem original_unitized_gns_eq_zero_of_extension_gns_eq_zero
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    {z : Unitization ℂ A}
    (hz : (positiveLinearMapOfMemStateSpace (unitizationExtension phi)
      (unitizationExtension_mem_stateSpace phi hphi)).gnsStarAlgHom z = 0) :
    (NonUnitalCStarRepresentation.unitization
      (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom) z = 0 := by
  let f := nonUnitalStatePositiveMap phi hphi
  let Phi := unitizationExtension phi
  let hPhi := unitizationExtension_mem_stateSpace phi hphi
  change Phi ∈ stateSpace (Unitization ℂ A) at hPhi
  let rho := (positiveLinearMapOfMemStateSpace Phi hPhi).gnsStarAlgHom
  have hdense : DenseRange (fun b : A => (f.toPreGNS b : f.GNS)) :=
    UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
      (UniformSpace.Completion.continuous_coe f.PreGNS)
  apply ContinuousLinearMap.ext
  intro y
  exact hdense.induction_on y (isClosed_eq (by fun_prop) continuous_const) fun b => by
    rw [unitized_gns_apply_toPreGNS]
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [nonUnital_gns_inner_toPreGNS]
    let c : A := z.fst • b + z.snd * b
    have hzc : (Unitization.inr c : Unitization ℂ A) = z * Unitization.inr b :=
      (unitization_mul_inr z b).symm
    have hzero : rho (star (Unitization.inr c) * Unitization.inr c) = 0 := by
      rw [hzc, map_mul, map_star, map_mul, hz]
      simp
    have hval := state_eq_zero_of_gnsStarAlgHom_eq_zero Phi hPhi hzero
    have hinr : star (Unitization.inr c : Unitization ℂ A) * Unitization.inr c =
        Unitization.inr (star c * c) := by
      let j := Unitization.inrNonUnitalStarAlgHom ℂ A
      change star (j c) * j c = j (star c * c)
      simp only [map_mul, map_star]
    rw [hinr] at hval
    simpa only [Phi, c, star_add, star_smul, star_mul] using
      (show (nonUnitalStatePositiveMap phi hphi) (star c * c) = 0 from by
        change phi (star c * c) = 0
        simpa [Phi] using hval)

/-- The essential bridge: equality of original GNS kernels gives equality
of canonical extended-state GNS kernels, with no simplicity assumption. -/
theorem unitizationExtension_stateGNSKernel_eq_of_nonUnital_gnsKernel_eq
    (phi psi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpsi : psi ∈ nonUnitalStateSpace A)
    (hker : ∀ a : A,
      (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom a = 0 ↔
      (nonUnitalStatePositiveMap psi hpsi).gnsNonUnitalStarAlgHom a = 0) :
    stateGNSKernel (unitizationExtension phi) =
      stateGNSKernel (unitizationExtension psi) := by
  have inclusion (phi psi : A →L[ℂ] ℂ)
      (hphi : phi ∈ nonUnitalStateSpace A) (hpsi : psi ∈ nonUnitalStateSpace A)
      (hinc : ∀ a : A,
        (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom a = 0 →
        (nonUnitalStatePositiveMap psi hpsi).gnsNonUnitalStarAlgHom a = 0) :
      stateGNSKernel (unitizationExtension phi) ⊆
        stateGNSKernel (unitizationExtension psi) := by
    intro z hz b
    let Phi := unitizationExtension phi
    let hPhi := unitizationExtension_mem_stateSpace phi hphi
    change Phi ∈ stateSpace (Unitization ℂ A) at hPhi
    let rho := (positiveLinearMapOfMemStateSpace Phi hPhi).gnsStarAlgHom
    have hrhoz : rho z = 0 := (mem_stateGNSKernel_iff Phi hPhi z).mp hz
    have hprod : rho (star (z * b) * (z * b)) = 0 := by
      simp only [map_mul, map_star, hrhoz, zero_mul, star_zero, mul_zero]
    have hsource := original_unitized_gns_eq_zero_of_extension_gns_eq_zero
      phi hphi hprod
    exact unitizationExtension_eq_zero_of_unitization_eq_zero
      (nonUnitalStatePositiveMap phi hphi).gnsNonUnitalStarAlgHom psi hpsi
      (fun a ha => nonUnitalState_eq_zero_of_gns_eq_zero psi hpsi (hinc a ha))
      hsource
  exact Set.Subset.antisymm
    (inclusion phi psi hphi hpsi (fun a => (hker a).mp))
    (inclusion psi phi hpsi hphi (fun a => (hker a).mpr))

/-- The same bridge in the representation-independent star-square language. -/
theorem unitizationExtension_stateGNSKernel_eq
    (phi psi : A →L[ℂ] ℂ) (hphi : phi ∈ nonUnitalStateSpace A)
    (hpsi : psi ∈ nonUnitalStateSpace A)
    (hker : nonUnitalStateGNSKernel phi = nonUnitalStateGNSKernel psi) :
    stateGNSKernel (unitizationExtension phi) =
      stateGNSKernel (unitizationExtension psi) := by
  apply unitizationExtension_stateGNSKernel_eq_of_nonUnital_gnsKernel_eq phi psi hphi hpsi
  intro a
  rw [← mem_nonUnitalStateGNSKernel_iff phi hphi a,
    ← mem_nonUnitalStateGNSKernel_iff psi hpsi a, hker]

end MathlibAnnex.Analysis.CStarAlgebra
