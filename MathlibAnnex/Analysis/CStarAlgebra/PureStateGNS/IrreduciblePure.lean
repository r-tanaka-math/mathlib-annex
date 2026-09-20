import Mathlib.Analysis.Normed.Operator.Extend
import MathlibAnnex.Analysis.CStarAlgebra.Intertwiner
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.PureIrreducible
import MathlibAnnex.Analysis.CStarAlgebra.Representation.PureStateRepresentatives

/-!
# Irreducible representations and pure vector states

The reverse pure-state/GNS implication is proved by extending the dominated
GNS orbit map to a contraction.  Its positive initial operator lies in the
commutant, so the arbitrary-dimensional Schur theorem makes it scalar.
-/

set_option autoImplicit false

open Set
open scoped ComplexOrder Convex InnerProduct

namespace MathlibAnnex.CStarAlgebra

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open MathlibAnnex.Analysis.CStarAlgebra

/-- A positive functional dominated by an irreducible unit vector state is a
real scalar multiple of that state.  The dominated functional may be zero;
no normalization or nonzero hypothesis is used. -/
theorem eq_smul_of_irreducible_vectorFunctional_of_nonnegative_le
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    (xi : H) (hxi : ‖xi‖ = 1)
    (rho : A →L[ℂ] ℂ) (hrho : ∀ a : A, 0 ≤ a → 0 ≤ rho a)
    (hle : ∀ a : A, 0 ≤ a → rho a ≤ Representation.vectorFunctional pi xi a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      rho = t • Representation.vectorFunctional pi xi := by
  letI : Nontrivial H := Representation.nontrivial_of_isNonzero pi hirr.1
  have hxi_ne : xi ≠ 0 := by
    intro hzero
    simpa [hzero] using hxi
  have hdense : DenseRange (StarAlgHom.orbitMap pi xi) :=
    Representation.denseRange_orbitMap_of_isIrreducible pi hirr hxi_ne
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ rho.toLinearMap hrho
  let sigma : Representation A f.GNS := f.gnsStarAlgHom
  let eta : f.GNS := f.gnsCyclicVector
  let p : A →ₗ[ℂ] H := StarAlgHom.orbitMap pi xi
  let q : A →ₗ[ℂ] f.GNS := StarAlgHom.orbitMap sigma eta
  have hq_inner (a : A) : inner ℂ (q a) (q a) = rho (star a * a) := by
    calc
      inner ℂ (q a) (q a) =
          Representation.vectorFunctional sigma eta (star a * a) := by
            simpa [p, q, StarAlgHom.orbitMap] using
              (Representation.vectorFunctional_star_mul sigma eta a a).symm
      _ = f (star a * a) := by
        exact PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f (star a * a)
      _ = rho (star a * a) := rfl
  have hp_inner (a : A) : inner ℂ (p a) (p a) =
      Representation.vectorFunctional pi xi (star a * a) := by
    simpa [p, StarAlgHom.orbitMap] using
      (Representation.vectorFunctional_star_mul pi xi a a).symm
  have hnorm (a : A) : ‖q a‖ ≤ (1 : ℝ) * ‖p a‖ := by
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (q a),
      norm_sq_eq_re_inner (𝕜 := ℂ) (p a), hq_inner, hp_inner]
    have hdiff := RCLike.nonneg_iff.mp
      (sub_nonneg.mpr (hle (star a * a) (star_mul_self_nonneg a)))
    simpa using hdiff.1
  let T : H →L[ℂ] f.GNS := q.extendOfNorm p
  have hT_orbit (a : A) : T (pi a xi) = sigma a eta := by
    simpa [T, p, q, StarAlgHom.orbitMap] using
      (LinearMap.extendOfNorm_eq hdense ⟨(1 : ℝ), hnorm⟩ a)
  have hT_intertwines : StarAlgHom.Intertwines pi sigma T := by
    intro b
    apply ContinuousLinearMap.ext
    intro x
    exact hdense.induction_on x
      (isClosed_eq ((T.comp (pi b)).continuous) (((sigma b).comp T).continuous))
      fun a ↦ by
        change T (pi b (pi a xi)) = sigma b (T (pi a xi))
        have hpi_mul : pi (b * a) xi = pi b (pi a xi) := by
          rw [map_mul]
          rfl
        have hsigma_mul : sigma (b * a) eta = sigma b (sigma a eta) := by
          rw [map_mul]
          rfl
        calc
          T (pi b (pi a xi)) = T (pi (b * a) xi) := congrArg T hpi_mul.symm
          _ = sigma (b * a) eta := hT_orbit (b * a)
          _ = sigma b (sigma a eta) := hsigma_mul
          _ = sigma b (T (pi a xi)) := by rw [hT_orbit a]
  let D : H →L[ℂ] H := (T†).comp T
  have hD_self : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hD_comm : StarAlgHom.InCommutant pi D := by
    exact hT_intertwines.inCommutant_adjoint_comp_self
  obtain ⟨t, hD⟩ := StarAlgHom.eq_algebraMap_of_isSelfAdjoint_of_irreducible
    pi (Representation.isIrreducible_starAlgHom pi hirr) D hD_self hD_comm
  have hTxi : T xi = eta := by
    simpa using hT_orbit (1 : A)
  have heta_sq : ‖eta‖ ^ 2 = (rho 1).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) eta]
    have hcoeff : inner ℂ eta eta = rho 1 := by
      calc
        inner ℂ eta eta = inner ℂ eta (sigma 1 eta) := by simp
        _ = f 1 := PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f 1
        _ = rho 1 := rfl
    rw [hcoeff]
    rw [RCLike.re_eq_complex_re]
  have ht_eq : t = (rho 1).re := by
    have hnormD := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right T xi
    rw [hTxi, heta_sq] at hnormD
    rw [show (T†).comp T = D by rfl, hD] at hnormD
    rw [ContinuousLinearMap.algebraMap_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right,
      RCLike.smul_re, ← norm_sq_eq_re_inner (𝕜 := ℂ), hxi] at hnormD
    simpa using hnormD.symm
  have ht_nonneg : 0 ≤ t := by
    rw [ht_eq]
    exact (RCLike.nonneg_iff.mp
      (hrho 1 (by simpa using star_mul_self_nonneg (1 : A)))).1
  have ht_le_one : t ≤ 1 := by
    rw [ht_eq]
    have hdiff := RCLike.nonneg_iff.mp
      (sub_nonneg.mpr (hle 1 (by simpa using star_mul_self_nonneg (1 : A))))
    simpa [Representation.vectorFunctional_one pi hxi] using hdiff.1
  refine ⟨t, ht_nonneg, ht_le_one, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  calc
    rho a = inner ℂ eta (sigma a eta) := by
      exact (PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f a).symm
    _ = inner ℂ (T xi) (sigma a (T xi)) := by rw [hTxi]
    _ = inner ℂ (T xi) (T (pi a xi)) := by
      have h := congrArg (fun R : H →L[ℂ] f.GNS ↦ R xi) (hT_intertwines a)
      simpa [ContinuousLinearMap.comp_apply] using congrArg (inner ℂ (T xi)) h.symm
    _ = inner ℂ xi (D (pi a xi)) := by
      simpa [D, ContinuousLinearMap.comp_apply] using
        (ContinuousLinearMap.adjoint_inner_right T xi (T (pi a xi))).symm
    _ = inner ℂ xi ((algebraMap ℝ (H →L[ℂ] H) t) (pi a xi)) := by rw [hD]
    _ = (t • Representation.vectorFunctional pi xi) a := by
      rw [ContinuousLinearMap.algebraMap_apply,
        RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
      simp [Representation.vectorFunctional_apply, Complex.real_smul]

/-- Every unit vector state of an explicitly nonzero irreducible unital
representation is pure. -/
theorem isPureState_vectorFunctional_of_isIrreducible
    (pi : Representation A H) (hirr : pi.IsIrreducible)
    (xi : H) (hxi : ‖xi‖ = 1) :
    IsPureState A (Representation.vectorFunctional pi xi) := by
  rw [IsPureState, mem_extremePoints_iff_left]
  refine ⟨vectorFunctional_mem_stateSpace pi xi hxi, ?_⟩
  intro psi hpsi chi hchi hsegment
  rcases hsegment with ⟨s, t, hs, ht, hst, hconv⟩
  let rho : A →L[ℂ] ℂ := s • psi
  have hrho : ∀ a : A, 0 ≤ a → 0 ≤ rho a := by
    intro a ha
    exact smul_nonneg hs.le (hpsi.1 a ha)
  have hle : ∀ a : A, 0 ≤ a →
      rho a ≤ Representation.vectorFunctional pi xi a := by
    intro a ha
    rw [← hconv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact le_add_of_nonneg_right (smul_nonneg ht.le (hchi.1 a ha))
  obtain ⟨r, -, -, hrho_eq⟩ :=
    eq_smul_of_irreducible_vectorFunctional_of_nonnegative_le
      pi hirr xi hxi rho hrho hle
  have hrs : r = s := by
    have h := congrArg (fun f : A →L[ℂ] ℂ ↦ f 1) hrho_eq
    have hre := congrArg Complex.re h
    simpa [rho, hpsi.2, Representation.vectorFunctional_one pi hxi,
      Complex.real_smul] using hre.symm
  apply smul_right_injective (A →L[ℂ] ℂ) hs.ne'
  simpa [rho, hrs] using hrho_eq

/-- Ordinary pure states are exactly those whose canonical GNS
representations are irreducible. -/
theorem isPureState_iff_gnsStarAlgHom_isIrreducible
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A) :
    IsPureState A phi ↔
      StarAlgHom.IsIrreducible
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom := by
  constructor
  · exact isIrreducible_pureState_gnsStarAlgHom phi hphi
  · intro hirr
    let f : A →ₚ[ℂ] ℂ := positiveLinearMapOfMemStateSpace phi hphi
    let xi : f.GNS := f.gnsCyclicVector
    have hxi : ‖xi‖ = 1 := by
      exact PositiveLinearMap.norm_gnsCyclicVector f
        (positiveLinearMapOfMemStateSpace_one phi hphi)
    have hxi_ne : xi ≠ 0 := by
      intro hzero
      simpa [hzero] using hxi
    letI : Nontrivial f.GNS := nontrivial_of_ne xi 0 hxi_ne
    have hirr' : Representation.IsIrreducible f.gnsStarAlgHom :=
      (Representation.isIrreducible_iff_starAlgHom f.gnsStarAlgHom).2 hirr
    have hpure := isPureState_vectorFunctional_of_isIrreducible
      f.gnsStarAlgHom hirr' xi hxi
    have hfunctional : Representation.vectorFunctional f.gnsStarAlgHom xi = phi := by
      apply ContinuousLinearMap.ext
      intro a
      exact inner_gnsStarAlgHom_stateGNSVector phi hphi a
    rw [hfunctional] at hpure
    exact hpure

/-- The existing chosen pure-GNS transversal covers every nonzero
irreducible representation on an arbitrary target Hilbert-space universe. -/
theorem irreducible_covered_by_pureState_representative
    (root : PureState A) (pi : Representation A H) (hirr : pi.IsIrreducible) :
    ∃ j : PureState.GNSClass A,
      Representation.UnitaryEquivalent pi
        (PureState.representative root j).positiveFunctional.gnsStarAlgHom := by
  obtain ⟨xi, hxi, hcyclic, -, hpi⟩ := irreducible_exists_vectorStateGNS pi hirr
  have hpure : IsPureState A (Representation.vectorFunctional pi xi) :=
    isPureState_vectorFunctional_of_isIrreducible pi hirr xi hxi
  let phi : PureState A := ⟨Representation.vectorFunctional pi xi, hpure⟩
  have hpositive : phi.positiveFunctional = vectorPositiveFunctional pi xi hxi := by
    ext a
    rfl
  have hpi' : Representation.UnitaryEquivalent pi phi.positiveFunctional.gnsStarAlgHom := by
    rw [hpositive]
    exact hpi
  have hrep : Representation.UnitaryEquivalent
      (PureState.representative root phi.classOf).positiveFunctional.gnsStarAlgHom
      phi.positiveFunctional.gnsStarAlgHom :=
    PureState.representative_covers root phi
  exact ⟨phi.classOf, Representation.unitaryEquivalent_trans hpi'
    (Representation.unitaryEquivalent_symm hrep)⟩

end MathlibAnnex.CStarAlgebra
