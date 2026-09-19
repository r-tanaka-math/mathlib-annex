import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import MathlibAnnex.Analysis.CStarAlgebra.GNSCyclic
import MathlibAnnex.Analysis.CStarAlgebra.Representation.VectorFunctional

/-!
# Pure states separated from closed ideals

This file supplies the functional-analytic existence theorem needed for
ordinary ideal separation.  It uses Hahn--Banach on the normed vector-space
quotient and Banach--Alaoglu/Krein--Milman on the weak-star state face.
-/

set_option autoImplicit false

open Metric Set
open scoped ComplexOrder Convex InnerProduct

namespace TwoSidedIdeal

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The complex subspace underlying a two-sided ideal in a complex algebra. -/
def complexSubmodule (I : TwoSidedIdeal A) : Submodule ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := fun hx hy => I.add_mem hx hy
  smul_mem' := fun c x hx => by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ hx

@[simp]
theorem mem_complexSubmodule (I : TwoSidedIdeal A) (x : A) :
    x ∈ I.complexSubmodule ↔ x ∈ I :=
  Iff.rfl

end TwoSidedIdeal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance weakDualIsScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance weakDualLocallyConvexSpace : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ
    (WeakBilin (topDualPairing ℂ A)))

/-- A contractive functional taking the value one at the identity is positive. -/
theorem nonnegative_of_norm_le_one_of_apply_one [Nontrivial A]
    (phi : A →L[ℂ] ℂ) (hnorm : ‖phi‖ ≤ 1) (hone : phi 1 = 1) :
    ∀ a : A, 0 ≤ a → 0 ≤ phi a := by
  have himag (a : A) (ha : IsSelfAdjoint a) : (phi a).im = 0 := by
    have hbound (t : ℝ) :
        ‖phi a‖ ^ 2 + 2 * (phi a).im * t ≤ ‖a‖ ^ 2 := by
      let x : A := a + ((t : ℂ) * Complex.I) • (1 : A)
      have hxstar : star x * x = a * a + (t ^ 2 : ℝ) • (1 : A) := by
        dsimp [x]
        let c : A := algebraMap ℂ A ((t : ℂ) * Complex.I)
        have hc : ((t : ℂ) * Complex.I) • (1 : A) = c := by
          simp [c, Algebra.smul_def]
        rw [hc, star_add, ha.star_eq]
        have hcstar : star c = -c := by
          rw [← hc, star_smul, star_one]
          simp
        rw [hcstar]
        have hcomm : c * a = a * c :=
          Algebra.commutes ((t : ℂ) * Complex.I) a
        rw [add_mul, mul_add, mul_add]
        simp only [neg_mul]
        rw [hcomm]
        have hcc : c * c = -((t ^ 2 : ℝ) • (1 : A)) := by
          rw [← hc, smul_mul_smul_comm]
          have hscalar :
              (t : ℂ) * Complex.I * ((t : ℂ) * Complex.I) =
                ((-(t ^ 2) : ℝ) : ℂ) := by
            push_cast
            ring_nf
            rw [Complex.I_sq]
            ring
          rw [hscalar]
          simp only [one_mul]
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
          simp
        rw [hcc]
        simp
      have hxnorm : ‖x‖ ^ 2 ≤ ‖a‖ ^ 2 + t ^ 2 := by
        calc
          ‖x‖ ^ 2 = ‖star x * x‖ := by
            simpa [pow_two] using (CStarRing.norm_star_mul_self (x := x)).symm
          _ = ‖a * a + (t ^ 2 : ℝ) • (1 : A)‖ := by rw [hxstar]
          _ ≤ ‖a * a‖ + ‖(t ^ 2 : ℝ) • (1 : A)‖ := norm_add_le _ _
          _ = ‖a‖ ^ 2 + t ^ 2 := by
            rw [ha.norm_mul_self]
            simp [norm_smul, norm_one]
      have hphi : ‖phi x‖ ≤ ‖x‖ := by
        calc
          ‖phi x‖ ≤ ‖phi‖ * ‖x‖ := phi.le_opNorm x
          _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
          _ = ‖x‖ := one_mul _
      have hsq : ‖phi x‖ ^ 2 ≤ ‖a‖ ^ 2 + t ^ 2 :=
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hphi).trans hxnorm
      have hvalue : phi x = phi a + ((t : ℂ) * Complex.I) := by
        simp [x, hone]
      rw [hvalue, Complex.sq_norm, Complex.normSq_apply] at hsq
      norm_num at hsq ⊢
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith
    by_contra hne
    let C : ℝ := ‖a‖ ^ 2 - (phi a).re ^ 2 - (phi a).im ^ 2
    let t : ℝ := (C + 1) / (2 * (phi a).im)
    have ht := hbound t
    have heq : 2 * (phi a).im * t = C + 1 := by
      dsimp [t]
      field_simp
    dsimp [C] at heq
    rw [Complex.sq_norm, Complex.normSq_apply] at ht
    nlinarith
  intro a ha
  apply RCLike.nonneg_iff.mpr
  refine ⟨?_, himag a ha.isSelfAdjoint⟩
  change 0 ≤ (phi a).re
  let b : A := algebraMap ℝ A ‖a‖ - a
  have hb : 0 ≤ b := by
    exact sub_nonneg.mpr (IsSelfAdjoint.le_algebraMap_norm_self ha.isSelfAdjoint)
  have hb_le : b ≤ algebraMap ℝ A ‖a‖ := by
    dsimp [b]
    exact sub_le_self _ ha
  have hbnorm : ‖b‖ ≤ ‖a‖ := by
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le hb hb_le
    simpa using h
  have hphib : ‖phi b‖ ≤ ‖b‖ := by
    calc
      ‖phi b‖ ≤ ‖phi‖ * ‖b‖ := phi.le_opNorm b
      _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖b‖ := one_mul _
  have hvalue : phi b = (‖a‖ : ℂ) - phi a := by
    dsimp [b]
    rw [map_sub]
    have hmapnorm : phi (algebraMap ℝ A ‖a‖) = (‖a‖ : ℂ) := by
      rw [show algebraMap ℝ A ‖a‖ = ‖a‖ • (1 : A) by simp [Algebra.smul_def]]
      rw [ContinuousLinearMap.map_smul_of_tower]
      simp [hone]
    rw [hmapnorm]
  have hreal : phi a = ((phi a).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using himag a ha.isSelfAdjoint
  rw [hvalue, hreal] at hphib
  have habs : |‖a‖ - (phi a).re| ≤ ‖a‖ := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
      hphib.trans hbnorm
  have hright := (abs_le.mp habs).2
  linarith

/-- The weak-star state space, using the ordinary normalized-positive predicate. -/
def weakStateSpace (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    Set (WeakDual ℂ A) :=
  {phi | (∀ a : A, 0 ≤ a → 0 ≤ phi a) ∧ phi 1 = 1}

/-- The weak-star face of states annihilating a two-sided ideal. -/
def weakStateFace (I : TwoSidedIdeal A) : Set (WeakDual ℂ A) :=
  {phi | phi ∈ weakStateSpace A ∧ ∀ x : A, x ∈ I → phi x = 0}

theorem isClosed_weakStateSpace : IsClosed (weakStateSpace A) := by
  simp only [weakStateSpace, setOf_and, setOf_forall]
  exact (isClosed_iInter fun a => isClosed_iInter fun _ha : 0 ≤ a =>
    isClosed_Ici.preimage (WeakDual.eval_continuous a)).inter
    (isClosed_singleton.preimage (WeakDual.eval_continuous 1))

theorem isClosed_weakStateFace (I : TwoSidedIdeal A) : IsClosed (weakStateFace I) := by
  simp only [weakStateFace, setOf_and, setOf_forall]
  exact isClosed_weakStateSpace.inter
    (isClosed_iInter fun x => isClosed_iInter fun _hx : x ∈ I =>
      isClosed_singleton.preimage (WeakDual.eval_continuous x))

theorem norm_le_one_of_mem_weakStateSpace
    {phi : WeakDual ℂ A} (hphi : phi ∈ weakStateSpace A) :
    ‖phi.toStrongDual‖ ≤ 1 := by
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ phi.toStrongDual.toLinearMap hphi.1
  let pi := f.gnsStarAlgHom
  let xi := f.gnsCyclicVector
  have hxi : ‖xi‖ = 1 := PositiveLinearMap.norm_gnsCyclicVector f hphi.2
  apply phi.toStrongDual.opNorm_le_bound zero_le_one
  intro a
  have hcoeff : inner ℂ xi (pi a xi) = phi a := by
    exact PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f a
  change ‖phi a‖ ≤ 1 * ‖a‖
  rw [← hcoeff]
  calc
    ‖inner ℂ xi (pi a xi)‖ ≤ ‖xi‖ * ‖pi a xi‖ := norm_inner_le_norm _ _
    _ = ‖pi a xi‖ := by rw [hxi, one_mul]
    _ ≤ ‖pi a‖ * ‖xi‖ := (pi a).le_opNorm xi
    _ = ‖pi a‖ := by rw [hxi, mul_one]
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le pi a
    _ = 1 * ‖a‖ := (one_mul _).symm

theorem weakStateFace_subset_closedBall (I : TwoSidedIdeal A) :
    weakStateFace I ⊆ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ A) 1 := by
  intro phi hphi
  simpa only [mem_preimage, mem_closedBall_zero_iff] using
    norm_le_one_of_mem_weakStateSpace hphi.1

/-- Vanishing of a positive functional on `x⋆x` forces vanishing on `x`. -/
theorem apply_eq_zero_of_star_mul_self_eq_zero
    (phi : A →L[ℂ] ℂ) (hphi : ∀ a : A, 0 ≤ a → 0 ≤ phi a)
    {x : A} (hx : phi (star x * x) = 0) : phi x = 0 := by
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ phi.toLinearMap hphi
  let pi := f.gnsStarAlgHom
  let xi := f.gnsCyclicVector
  have hinner : inner ℂ (pi x xi) (pi x xi) = phi (star x * x) := by
    calc
      inner ℂ (pi x xi) (pi x xi) =
          Representation.vectorFunctional pi xi (star x * x) := by
        simpa using (Representation.vectorFunctional_star_mul pi xi x x).symm
      _ = f (star x * x) :=
        PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f (star x * x)
      _ = phi (star x * x) := rfl
  have hvec : pi x xi = 0 := inner_self_eq_zero.mp (hinner.trans hx)
  calc
    phi x = f x := rfl
    _ = inner ℂ xi (pi x xi) :=
      (PositiveLinearMap.inner_gnsCyclicVector_gnsStarAlgHom f x).symm
    _ = 0 := by rw [hvec, inner_zero_right]

theorem isExtreme_weakStateFace (I : TwoSidedIdeal A) :
    IsExtreme ℝ (weakStateSpace A) (weakStateFace I) := by
  refine ⟨fun _ h => h.1, ?_⟩
  intro psi hpsi theta htheta phi hface hseg
  refine ⟨hpsi, ?_⟩
  intro x hx
  have hxx : star x * x ∈ I := I.mul_mem_left (star x) x hx
  rcases hseg with ⟨s, t, hs, ht, hst, hconv⟩
  have hvalue := congrArg (fun f : WeakDual ℂ A => f (star x * x)) hconv
  change s • psi (star x * x) + t • theta (star x * x) =
    phi (star x * x) at hvalue
  have hzero : s * (psi (star x * x)).re + t * (theta (star x * x)).re = 0 := by
    have := congrArg Complex.re hvalue
    simpa [hface.2 (star x * x) hxx, Complex.real_smul] using this
  have hpsi_nonneg := RCLike.nonneg_iff.mp
    (hpsi.1 (star x * x) (star_mul_self_nonneg x))
  have htheta_nonneg := RCLike.nonneg_iff.mp
    (htheta.1 (star x * x) (star_mul_self_nonneg x))
  have hpsi_re : (psi (star x * x)).re = 0 := by
    have hpsi_re_nonneg : 0 ≤ (psi (star x * x)).re := hpsi_nonneg.1
    have htheta_re_nonneg : 0 ≤ (theta (star x * x)).re := htheta_nonneg.1
    nlinarith
  have hpsi_xx : psi (star x * x) = 0 := by
    apply Complex.ext
    · simpa using hpsi_re
    · simpa using hpsi_nonneg.2
  exact apply_eq_zero_of_star_mul_self_eq_zero psi.toStrongDual hpsi.1 hpsi_xx

theorem isCompact_weakStateFace (I : TwoSidedIdeal A) : IsCompact (weakStateFace I) :=
  (WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := A) 0 1).of_isClosed_subset
    (isClosed_weakStateFace I) (weakStateFace_subset_closedBall I)

omit [PartialOrder A] [StarOrderedRing A] in
private theorem nonunit_of_mem_proper
    (I : TwoSidedIdeal A) (hI : I ≠ ⊤) {x : A} (hx : x ∈ I) : x ∈ nonunits A := by
  rw [mem_nonunits_iff]
  intro hunit
  obtain ⟨u, rfl⟩ := hunit
  apply hI
  apply I.eq_top
  rw [← u.inv_mul]
  exact I.mul_mem_left (u⁻¹ : Aˣ) (u : A) hx

omit [PartialOrder A] [StarOrderedRing A] in
private theorem quotient_one_norm
    (I : TwoSidedIdeal A) (hI : I ≠ ⊤) :
    ‖(Submodule.Quotient.mk (1 : A) : A ⧸ I.complexSubmodule)‖ = 1 := by
  letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp fun hsub => by
    letI : Subsingleton A := hsub
    apply hI
    apply I.eq_top
    have h10 : (1 : A) = 0 := Subsingleton.elim _ _
    rw [h10]
    exact I.zero_mem
  apply le_antisymm
  · simpa only [CStarRing.norm_one] using
      Submodule.Quotient.norm_mk_le I.complexSubmodule (1 : A)
  · change 1 ≤
      ‖(QuotientAddGroup.mk (1 : A) : A ⧸ I.complexSubmodule.toAddSubgroup)‖
    rw [QuotientAddGroup.norm_mk, Submodule.coe_toAddSubgroup]
    change 1 ≤ Metric.infDist (1 : A) (I.complexSubmodule : Set A)
    apply (Metric.le_infDist (s := (I.complexSubmodule : Set A))
      ⟨0, I.zero_mem⟩).2
    intro x hx
    have hx' : x ∈ nonunits A := nonunit_of_mem_proper I hI hx
    have hnot := nonunits.subset_compl_ball hx'
    rw [mem_compl_iff, mem_ball] at hnot
    simpa [dist_comm] using le_of_not_gt hnot

/-- Hahn--Banach produces a genuine state annihilating every proper closed
two-sided ideal. -/
theorem exists_state_annihilating
    [Nontrivial A] (I : TwoSidedIdeal A) (hI : I ≠ ⊤)
    (hclosed : IsClosed (I : Set A)) :
    ∃ phi : A →L[ℂ] ℂ,
      (∀ a : A, 0 ≤ a → 0 ≤ phi a) ∧ phi 1 = 1 ∧
        ∀ x : A, x ∈ I → phi x = 0 := by
  let J := I.complexSubmodule
  letI : IsClosed (J : Set A) := hclosed
  let q : A →L[ℂ] A ⧸ J := LinearMap.mkContinuous J.mkQ 1 fun a => by
    change ‖(Submodule.Quotient.mk a : A ⧸ J)‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le J a
  have hqone : ‖q (1 : A)‖ = 1 := by
    simpa [q, J] using quotient_one_norm I hI
  obtain ⟨g, hg_norm, hg_one⟩ := exists_dual_vector ℂ (q (1 : A)) (by simp [hqone])
  let phi : A →L[ℂ] ℂ := g.comp q
  have hphi_norm : ‖phi‖ ≤ 1 := by
    apply phi.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖phi a‖ ≤ ‖g‖ * ‖q a‖ := g.le_opNorm (q a)
      _ = ‖q a‖ := by rw [hg_norm, one_mul]
      _ ≤ ‖a‖ := by
        change ‖(Submodule.Quotient.mk a : A ⧸ J)‖ ≤ ‖a‖
        exact Submodule.Quotient.norm_mk_le J a
      _ = 1 * ‖a‖ := (one_mul _).symm
  have hphi_one : phi 1 = 1 := by
    dsimp [phi]
    rw [hg_one, hqone]
    norm_num
  refine ⟨phi, nonnegative_of_norm_le_one_of_apply_one phi hphi_norm hphi_one,
    hphi_one, ?_⟩
  intro x hx
  dsimp [phi, q]
  have hqx : (Submodule.Quotient.mk x : A ⧸ J) = 0 :=
    (Submodule.Quotient.mk_eq_zero J).mpr hx
  rw [hqx, map_zero]

theorem weakStateFace_nonempty
    [Nontrivial A] (I : TwoSidedIdeal A) (hI : I ≠ ⊤)
    (hclosed : IsClosed (I : Set A)) : (weakStateFace I).Nonempty := by
  obtain ⟨phi, hpos, hone, hann⟩ := exists_state_annihilating I hI hclosed
  exact ⟨StrongDual.toWeakDual phi, ⟨⟨hpos, hone⟩, hann⟩⟩

/-- Every proper closed two-sided ideal is annihilated by an extreme state. -/
theorem exists_extreme_state_annihilating
    [Nontrivial A] (I : TwoSidedIdeal A) (hI : I ≠ ⊤)
    (hclosed : IsClosed (I : Set A)) :
    ∃ phi : A →L[ℂ] ℂ,
      phi ∈ ({psi : A →L[ℂ] ℂ |
        (∀ a : A, 0 ≤ a → 0 ≤ psi a) ∧ psi 1 = 1}).extremePoints ℝ ∧
      ∀ x : A, x ∈ I → phi x = 0 := by
  obtain ⟨f, hfext⟩ := (isCompact_weakStateFace I).extremePoints_nonempty
    (weakStateFace_nonempty I hI hclosed)
  have hfstate : f ∈ (weakStateSpace A).extremePoints ℝ :=
    (isExtreme_weakStateFace I).extremePoints_subset_extremePoints hfext
  refine ⟨f.toStrongDual, ?_, hfext.1.2⟩
  rw [mem_extremePoints_iff_left] at hfstate ⊢
  refine ⟨hfstate.1, ?_⟩
  intro psi hpsi theta htheta hseg
  let psi' : WeakDual ℂ A := StrongDual.toWeakDual psi
  let theta' : WeakDual ℂ A := StrongDual.toWeakDual theta
  have hpsi' : psi' ∈ weakStateSpace A := hpsi
  have htheta' : theta' ∈ weakStateSpace A := htheta
  have hseg' : f ∈ openSegment ℝ psi' theta' := by
    rcases hseg with ⟨s, t, hs, ht, hst, hconv⟩
    refine ⟨s, t, hs, ht, hst, ?_⟩
    apply DFunLike.ext _ _
    intro a
    change s • psi a + t • theta a = f a
    exact congrArg (fun q : StrongDual ℂ A => q a) hconv
  have heq : psi' = f := hfstate.2 psi' hpsi' theta' htheta' hseg'
  apply ContinuousLinearMap.ext
  intro a
  exact congrArg (fun q : WeakDual ℂ A => q a) heq

end MathlibAnnex.Analysis.CStarAlgebra
