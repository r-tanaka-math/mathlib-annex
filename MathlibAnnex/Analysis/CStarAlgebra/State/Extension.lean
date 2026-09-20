import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Module.HahnBanach
import MathlibAnnex.Analysis.CStarAlgebra.PureState
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic

/-!
# Pure extension of characters

Characters of a unital C-star subalgebra are pure states.  Hahn--Banach and
Krein--Milman then give a pure state of the ambient algebra extending any
such character.
-/

set_option autoImplicit false

open Metric Set
open scoped ComplexOrder Convex

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance extensionWeakDualIsScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ A))

local instance extensionWeakDualLocallyConvexSpace : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ A)))

/-- A continuous character of a unital C-star algebra is positive. -/
theorem character_nonnegative (chi : WeakDual.characterSpace ℂ A) :
    ∀ a : A, 0 ≤ a → 0 ≤ chi a := by
  intro a ha
  rw [StarOrderedRing.nonneg_iff] at ha ⊢
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      refine AddSubmonoid.subset_closure ⟨chi b, ?_⟩
      rw [map_mul, map_star]
  | zero => simp
  | add x y _ _ hx hy => simpa using AddSubmonoid.add_mem _ hx hy

/-- A character, regarded as a continuous linear functional, is a state. -/
theorem character_mem_stateSpace (chi : WeakDual.characterSpace ℂ A) :
    WeakDual.CharacterSpace.toCLM chi ∈ stateSpace A :=
  ⟨character_nonnegative chi, map_one chi⟩

/-- Every character of a unital C-star algebra is a pure state. -/
theorem isPureState_character (chi : WeakDual.characterSpace ℂ A) :
    IsPureState A (WeakDual.CharacterSpace.toCLM chi) := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨character_mem_stateSpace chi, ?_⟩
  intro psi hpsi theta htheta hseg
  rcases hseg with ⟨s, t, hs, ht, hst, hconv⟩
  have endpoint (rho : A →L[ℂ] ℂ) (hrho : rho ∈ stateSpace A)
      (other : A →L[ℂ] ℂ) (hother : other ∈ stateSpace A)
      (r q : ℝ) (hr : 0 < r) (hq : 0 < q)
      (hconv' : r • rho + q • other = WeakDual.CharacterSpace.toCLM chi) :
      rho = WeakDual.CharacterSpace.toCLM chi := by
    apply ContinuousLinearMap.ext
    intro a
    let x : A := a - algebraMap ℂ A (chi a)
    have hchix : chi x = 0 := by
      have hc : chi (algebraMap ℂ A (chi a)) = chi a := by
        simpa using AlgHomClass.commutes chi (chi a)
      calc
        chi x = chi a - chi (algebraMap ℂ A (chi a)) := by
          simp only [x, map_sub]
        _ = chi a - chi a := by rw [hc]
        _ = 0 := sub_self _
    have hchixx : chi (star x * x) = 0 := by
      rw [map_mul, map_star, hchix]
      simp
    have hvalue := congrArg (fun f : A →L[ℂ] ℂ => f (star x * x)) hconv'
    change r • rho (star x * x) + q • other (star x * x) =
      chi (star x * x) at hvalue
    have hzero :
        r * (rho (star x * x)).re + q * (other (star x * x)).re = 0 := by
      have := congrArg Complex.re hvalue
      simpa [hchixx, Complex.real_smul] using this
    have hrho_nonneg := RCLike.nonneg_iff.mp
      (hrho.1 (star x * x) (star_mul_self_nonneg x))
    have hother_nonneg := RCLike.nonneg_iff.mp
      (hother.1 (star x * x) (star_mul_self_nonneg x))
    have hrho_re : (rho (star x * x)).re = 0 := by
      have hleft : 0 ≤ r * (rho (star x * x)).re :=
        mul_nonneg hr.le hrho_nonneg.1
      have hright : 0 ≤ q * (other (star x * x)).re :=
        mul_nonneg hq.le hother_nonneg.1
      have hmul : r * (rho (star x * x)).re = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_left hr.ne'
    have hrho_xx : rho (star x * x) = 0 := by
      apply Complex.ext
      · simpa using hrho_re
      · simpa using hrho_nonneg.2
    have hrho_x : rho x = 0 :=
      apply_eq_zero_of_star_mul_self_eq_zero rho hrho.1 hrho_xx
    calc
      rho a = rho (x + algebraMap ℂ A (chi a)) := by simp [x]
      _ = rho x + rho (algebraMap ℂ A (chi a)) := map_add rho _ _
      _ = chi a := by
        rw [hrho_x, zero_add, Algebra.algebraMap_eq_smul_one, map_smul, hrho.2]
        simp
      _ = WeakDual.CharacterSpace.toCLM chi a := rfl
  have hpsi_eq : psi = WeakDual.CharacterSpace.toCLM chi :=
    endpoint psi hpsi theta htheta s t hs ht hconv
  have htheta_eq : theta = WeakDual.CharacterSpace.toCLM chi :=
    endpoint theta htheta psi hpsi t s ht hs (by simpa [add_comm] using hconv)
  exact ⟨hpsi_eq, htheta_eq⟩

section Extension

variable [Nontrivial A]

/-- Weak-star states whose restriction to `D` equals `chi`. -/
def weakStateExtensionFace (D : StarSubalgebra ℂ A)
    (chi : WeakDual.characterSpace ℂ D) : Set (WeakDual ℂ A) :=
  {phi | phi ∈ weakStateSpace A ∧ ∀ d : D, phi d = chi d}

private theorem character_norm_eq_one (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    ‖WeakDual.CharacterSpace.toCLM chi‖ = 1 := by
  apply le_antisymm
  · change ‖WeakDual.toStrongDual (chi : WeakDual ℂ D)‖ ≤ 1
    simpa using WeakDual.CharacterSpace.norm_le_norm_one chi
  · have h := (WeakDual.CharacterSpace.toCLM chi).le_opNorm (1 : D)
    simpa using h

/-- Hahn--Banach extends a character to an ambient state. -/
theorem exists_state_extension (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    ∃ phi : A →L[ℂ] ℂ, phi ∈ stateSpace A ∧ ∀ d : D, phi d = chi d := by
  let p : Submodule ℂ A := D.toSubalgebra.toSubmodule
  let f : StrongDual ℂ p := WeakDual.CharacterSpace.toCLM chi
  obtain ⟨phi, hext, hnorm⟩ := exists_extension_norm_eq p f
  have hfone : f (⟨1, D.one_mem⟩ : p) = 1 := by
    change chi (1 : D) = 1
    exact map_one chi
  have hphi_one : phi 1 = 1 := by
    calc
      phi 1 = f (⟨1, D.one_mem⟩ : p) := hext (⟨1, D.one_mem⟩ : p)
      _ = 1 := hfone
  have hphi_norm : ‖phi‖ ≤ 1 := by
    rw [hnorm]
    exact le_of_eq (character_norm_eq_one D chi)
  refine ⟨phi, ⟨nonnegative_of_norm_le_one_of_apply_one phi hphi_norm hphi_one,
    hphi_one⟩, ?_⟩
  intro d
  simpa [p, f] using hext (show p from d)

theorem isClosed_weakStateExtensionFace (D : StarSubalgebra ℂ A)
    (chi : WeakDual.characterSpace ℂ D) :
    IsClosed (weakStateExtensionFace D chi) := by
  simp only [weakStateExtensionFace, setOf_and, setOf_forall]
  exact isClosed_weakStateSpace.inter
    (isClosed_iInter fun d =>
      isClosed_eq (WeakDual.eval_continuous (d : A)) continuous_const)

theorem weakStateExtensionFace_subset_closedBall (D : StarSubalgebra ℂ A)
    (chi : WeakDual.characterSpace ℂ D) :
    weakStateExtensionFace D chi ⊆
      WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℂ A) 1 := by
  intro phi hphi
  simpa only [mem_preimage, mem_closedBall_zero_iff] using
    norm_le_one_of_mem_weakStateSpace hphi.1

theorem isCompact_weakStateExtensionFace (D : StarSubalgebra ℂ A)
    (chi : WeakDual.characterSpace ℂ D) :
    IsCompact (weakStateExtensionFace D chi) :=
  (WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := A) 0 1).of_isClosed_subset
    (isClosed_weakStateExtensionFace D chi)
    (weakStateExtensionFace_subset_closedBall D chi)

theorem weakStateExtensionFace_nonempty (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    (weakStateExtensionFace D chi).Nonempty := by
  obtain ⟨phi, hphi, hext⟩ := exists_state_extension D chi
  exact ⟨StrongDual.toWeakDual phi, hphi, hext⟩

/-- The extension set is a face of the ambient state space. -/
theorem isExtreme_weakStateExtensionFace (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    IsExtreme ℝ (weakStateSpace A) (weakStateExtensionFace D chi) := by
  let spectralOrderD : PartialOrder D := CStarAlgebra.spectralOrder D
  letI : LE D := spectralOrderD.toLE
  letI : LT D := spectralOrderD.toLT
  letI : PartialOrder D := spectralOrderD
  letI : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  have coe_nonnegative {d : D} (hd : 0 ≤ d) : 0 ≤ (d : A) := by
    rw [StarOrderedRing.nonneg_iff] at hd
    induction hd using AddSubmonoid.closure_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        simpa using star_mul_self_nonneg (y : A)
    | zero => simp
    | add x y _ _ hx hy =>
        simpa using add_nonneg hx hy
  refine ⟨fun _ h => h.1, ?_⟩
  intro psi hpsi theta htheta phi hphi hseg
  refine ⟨hpsi, ?_⟩
  let p : Submodule ℂ A := D.toSubalgebra.toSubmodule
  let psiD : D →L[ℂ] ℂ := psi.toStrongDual.comp p.subtypeL
  let thetaD : D →L[ℂ] ℂ := theta.toStrongDual.comp p.subtypeL
  have hpsiD : psiD ∈ stateSpace D := by
    refine ⟨?_, ?_⟩
    · intro d hd
      exact hpsi.1 (d : A) (coe_nonnegative hd)
    · exact hpsi.2
  have hthetaD : thetaD ∈ stateSpace D := by
    refine ⟨?_, ?_⟩
    · intro d hd
      exact htheta.1 (d : A) (coe_nonnegative hd)
    · exact htheta.2
  have hchi := isPureState_character chi
  rw [IsPureState, mem_extremePoints] at hchi
  have hsegD : WeakDual.CharacterSpace.toCLM chi ∈
      openSegment ℝ psiD thetaD := by
    rcases hseg with ⟨s, t, hs, ht, hst, hconv⟩
    refine ⟨s, t, hs, ht, hst, ?_⟩
    apply ContinuousLinearMap.ext
    intro d
    have hv := congrArg (fun q : WeakDual ℂ A => q (d : A)) hconv
    change s • psi (d : A) + t • theta (d : A) = phi (d : A) at hv
    change s • psi (d : A) + t • theta (d : A) = chi d
    simpa only [hphi.2 d] using hv
  have hends := hchi.2 psiD hpsiD thetaD hthetaD hsegD
  intro d
  exact congrArg (fun q : D →L[ℂ] ℂ => q d) hends.1

/-- Every character of a unital star subalgebra has a pure state extension
to the ambient C-star algebra. -/
theorem exists_pureState_extension (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (chi : WeakDual.characterSpace ℂ D) :
    ∃ phi : A →L[ℂ] ℂ,
      phi ∈ stateSpace A ∧ IsPureState A phi ∧ ∀ d : D, phi d = chi d := by
  obtain ⟨f, hfext⟩ := (isCompact_weakStateExtensionFace D chi).extremePoints_nonempty
    (weakStateExtensionFace_nonempty D chi)
  have hfstate : f ∈ (weakStateSpace A).extremePoints ℝ :=
    (isExtreme_weakStateExtensionFace D chi).extremePoints_subset_extremePoints hfext
  refine ⟨f.toStrongDual, hfext.1.1, ?_, hfext.1.2⟩
  rw [IsPureState, mem_extremePoints_iff_left]
  rw [mem_extremePoints_iff_left] at hfstate
  refine ⟨hfstate.1, ?_⟩
  intro psi hpsi theta htheta hseg
  let psi' : WeakDual ℂ A := StrongDual.toWeakDual psi
  let theta' : WeakDual ℂ A := StrongDual.toWeakDual theta
  have hseg' : f ∈ openSegment ℝ psi' theta' := by
    rcases hseg with ⟨s, t, hs, ht, hst, hconv⟩
    refine ⟨s, t, hs, ht, hst, ?_⟩
    apply DFunLike.ext _ _
    intro a
    change s • psi a + t • theta a = f a
    exact congrArg (fun q : StrongDual ℂ A => q a) hconv
  have heq : psi' = f := hfstate.2 psi' hpsi theta' htheta hseg'
  apply ContinuousLinearMap.ext
  intro a
  exact congrArg (fun q : WeakDual ℂ A => q a) heq

end Extension

end MathlibAnnex.Analysis.CStarAlgebra
