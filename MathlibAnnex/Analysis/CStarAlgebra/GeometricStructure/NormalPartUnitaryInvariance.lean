/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.SingletonFiniteConjugation
import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.NormalPartBounded
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# Unitary multiplication invariance from finite-conjugation tests

The test source is the full algebra of bounded operators with its actual
nonzero irreducible identity action. Its range is proved equal to top.
The comparison f uses the identity on both vector coordinates and needs only
S <= B(H) for FORWARD full continuity. A bounded invertible pair defines a
particular source self-homeomorphism g. The TEST PROPERTY, not inverse
continuity of f, supplies both full continuities of f g f^-1.

The coefficient formula identifies that very conjugate with the original
normal-part map on S. The existing two-direction criterion then gives the
sandwich image equality. For unitaries, choosing V = W* and U = id gives
left multiplication by W; choosing U = W and V = id gives right multiplication.
The fixed four-unitary decomposition gives ideal INCLUSIONS for arbitrary
operators, never equality for the zero multiplier. S is not assumed unital.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] HomKernelQuotient.imageCStarAlgebra HomKernelQuotient.isClosed_image

/-- The identity action of the actual full operator algebra. -/
def operatorIdentityRepresentation : NonUnitalCStarRepresentation (H →L[ℂ] H) H :=
  NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)

@[simp]
theorem operatorIdentityRepresentation_apply (a : H →L[ℂ] H) :
    operatorIdentityRepresentation a = a := rfl

/-- The range is proved to be the full concrete subalgebra; the two types are
not identified merely because their names denote B(H). -/
theorem range_operatorIdentityRepresentation :
    NonUnitalStarAlgHom.range (operatorIdentityRepresentation (H := H)) = ⊤ := by
  ext a
  change (∃ b : H →L[ℂ] H, b = a) ↔ True
  simp

/-- Every invariant subspace of the full action that contains a nonzero x
contains every y, by a normalized rank-one operator sending x to y. -/
theorem isIrreducible_operatorIdentityRepresentation [Nontrivial H] :
    (operatorIdentityRepresentation (H := H)).IsIrreducible := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact hx (congrArg (fun a : H →L[ℂ] H => a x) h)
  · intro L hL
    by_cases hbot : L = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨x, hxL, hx⟩ : ∃ x : H, x ∈ L ∧ x ≠ 0 := by
      by_contra! h
      apply hbot
      apply le_antisymm ?_ bot_le
      intro x hxL
      change x = 0
      exact h x hxL
    apply top_unique
    intro y _
    have hc : inner ℂ x x ≠ 0 := by
      intro hxx
      exact hx ((inner_self_eq_zero (𝕜 := ℂ)).mp hxx)
    let a : H →L[ℂ] H := (inner ℂ x x)⁻¹ • InnerProductSpace.rankOne ℂ y x
    have ha := (hL.2 a x hxL).1
    change a x ∈ L at ha
    simpa only [a, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
      smul_smul, inv_mul_cancel₀ hc, one_smul] using ha

variable (S : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
variable [IsClosed (S : Set (H →L[ℂ] H))]
variable (hS : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype S))

/-- A concrete conjugation test on B(H) yields the two full continuities on S.
The source algebra and its represented Hilbert space both have universe u. -/
theorem continuous_normalPartLinearMap_and_inverse_of_finiteConjugation
    (hc : ClosureSpace.HasImageNormalPartFiniteConjugation.{u, u, u}
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (U V : H ≃L[ℂ] H) :
    (((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (normalPartSemilinearMap S S hS U.toLinearEquiv V.toLinearEquiv) ∧
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)).Continuous
        ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S))
        (normalPartSemilinearMap S S hS U.symm.toLinearEquiv V.symm.toLinearEquiv)) := by
  letI : Nontrivial H := NonUnitalCStarRepresentation.nontrivial_of_isNonzero
    (NonUnitalStarSubalgebraClass.subtype S) hS.1
  letI : PartialOrder (H →L[ℂ] H) := _root_.CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (H →L[ℂ] H) := _root_.CStarAlgebra.spectralOrderedRing _
  let pi := operatorIdentityRepresentation (H := H)
  have hpi : pi.IsIrreducible := isIrreducible_operatorIdentityRepresentation
  let Q := (NonUnitalStarAlgHom.range pi)
  have hQ : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype Q) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff pi).mpr hpi
  have htop : Q = ⊤ := range_operatorIdentityRepresentation
  let d := (NormedSpace.geometricStructureClosure ℂ Q).subspace (normalPart Q)
  let c := (NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)
  let idH : H ≃L[ℂ] H := ContinuousLinearEquiv.refl ℂ H
  let f := normalPartLinearFiniteHomeomorph Q S hQ hS idH.toLinearEquiv idH.toLinearEquiv
  have hf : d.Continuous c f.toEquiv := by
    apply (continuous_normalPartLinearMap_iff Q S hQ hS idH idH).mpr
    intro b
    simp [htop]
  let g := normalPartLinearFiniteHomeomorph Q Q hQ hQ U.toLinearEquiv V.toLinearEquiv
  have hg : d.Continuous d g.toEquiv := by
    apply (continuous_normalPartLinearMap_iff Q Q hQ hQ U V).mpr
    intro b
    simp [htop]
  have hgInv : d.Continuous d g.toEquiv.symm := by
    apply (continuous_normalPartLinearMap_iff Q Q hQ hQ U.symm V.symm).mpr
    intro b
    simp [htop]
  let gFull : ClosureSpace.Homeomorph d d :=
    { toEquiv := g.toEquiv
      continuous_toFun := hg
      continuous_invFun := hgInv }
  have hh := hc (H →L[ℂ] H) H pi hpi f hf g gFull.continuous_toFun
  have heq : (f.conjugate g).toEquiv =
      normalPartSemilinearEquiv S S hS hS (fun _ => rfl) U.toLinearEquiv V.toLinearEquiv := by
    apply Equiv.ext
    intro I
    obtain ⟨x, y, hx, hy, rfl⟩ := exists_normalPartPoint_eq S hS I
    change normalPartSemilinearMap Q S hS idH.toLinearEquiv idH.toLinearEquiv
      (normalPartSemilinearMap Q Q hQ U.toLinearEquiv V.toLinearEquiv
        (normalPartSemilinearMap S Q hQ idH.symm.toLinearEquiv idH.symm.toLinearEquiv
          (normalPartPoint S hS x y hx hy))) =
      normalPartSemilinearMap S S hS U.toLinearEquiv V.toLinearEquiv
        (normalPartPoint S hS x y hx hy)
    rw [normalPartSemilinearMap_point S Q hS hQ (fun _ => rfl),
      normalPartSemilinearMap_point Q Q hQ hQ (fun _ => rfl),
      normalPartSemilinearMap_point Q S hQ hS (fun _ => rfl),
      normalPartSemilinearMap_point S S hS hS (fun _ => rfl)]
    rfl
  rw [heq] at hh
  exact hh

include hS in
/-- The existing two-continuity criterion gives an actual image equality.
This stronger intermediate statement permits any bounded invertible pair. -/
theorem adjointSandwich_image_eq_of_finiteConjugation
    (hc : ClosureSpace.HasImageNormalPartFiniteConjugation.{u, u, u}
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (U V : H ≃L[ℂ] H) :
    InnerProductSpace.adjointSandwich U.toContinuousLinearMap V.toContinuousLinearMap ''
      (S : Set (H →L[ℂ] H)) = (S : Set (H →L[ℂ] H)) :=
  (continuous_normalPartLinearMap_and_inverse_iff S S hS hS U V).mp
    (continuous_normalPartLinearMap_and_inverse_of_finiteConjugation S hS hc U V)

include hS in
/-- The unitary test with U=id and V=W* is LEFT multiplication by W,
whereas U=W and V=id is RIGHT multiplication. No unit of S is assumed. -/
theorem unitary_mul_image_eq_of_finiteConjugation
    (hc : ClosureSpace.HasImageNormalPartFiniteConjugation.{u, u, u}
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (W : unitary (H →L[ℂ] H)) :
    (fun a : H →L[ℂ] H => (W : H →L[ℂ] H) * a) '' (S : Set (H →L[ℂ] H)) = S ∧
      (fun a : H →L[ℂ] H => a * (W : H →L[ℂ] H)) '' (S : Set (H →L[ℂ] H)) = S := by
  let idH : H ≃L[ℂ] H := ContinuousLinearEquiv.refl ℂ H
  let Wc : H ≃L[ℂ] H := (Unitary.linearIsometryEquiv W).toContinuousLinearEquiv
  let Wsc : H ≃L[ℂ] H := (Unitary.linearIsometryEquiv (star W)).toContinuousLinearEquiv
  have hleft := adjointSandwich_image_eq_of_finiteConjugation S hS hc idH Wsc
  have hright := adjointSandwich_image_eq_of_finiteConjugation S hS hc Wc idH
  have hlf : InnerProductSpace.adjointSandwich idH.toContinuousLinearMap Wsc.toContinuousLinearMap =
      (fun a : H →L[ℂ] H => (W : H →L[ℂ] H) * a) := by
    funext a
    change (star (star (W : H →L[ℂ] H))).comp (a.comp (ContinuousLinearMap.id ℂ H)) =
      (W : H →L[ℂ] H) * a
    rw [star_star, ContinuousLinearMap.comp_id]
    rfl
  have hrf : InnerProductSpace.adjointSandwich Wc.toContinuousLinearMap idH.toContinuousLinearMap =
      (fun a : H →L[ℂ] H => a * (W : H →L[ℂ] H)) := by
    funext a
    change (ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ H)).comp
      (a.comp (W : H →L[ℂ] H)) = a * (W : H →L[ℂ] H)
    rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp]
    rfl
  exact ⟨hlf ▸ hleft, hrf ▸ hright⟩

include hS in
/-- Four actual unitaries span any bounded operator. The resulting ideal
condition is a pair of inclusions, not equality for arbitrary multipliers. -/
theorem mul_mem_of_finiteConjugation
    (hc : ClosureSpace.HasImageNormalPartFiniteConjugation.{u, u, u}
      ((NormedSpace.geometricStructureClosure ℂ S).subspace (normalPart S)))
    (b : H →L[ℂ] H) {a : H →L[ℂ] H} (ha : a ∈ S) :
    b * a ∈ S ∧ a * b ∈ S := by
  obtain ⟨W, c, rfl, _⟩ := _root_.CStarAlgebra.exists_sum_four_unitary b
  constructor
  · rw [Finset.sum_mul]
    apply S.sum_mem
    intro i _
    rw [smul_mul_assoc]
    apply S.smul_mem
    have heq := (unitary_mul_image_eq_of_finiteConjugation S hS hc (W i)).1
    change (W i : H →L[ℂ] H) * a ∈ (S : Set (H →L[ℂ] H))
    rw [← heq]
    exact ⟨a, ha, rfl⟩
  · rw [Finset.mul_sum]
    apply S.sum_mem
    intro i _
    rw [mul_smul_comm]
    apply S.smul_mem
    have heq := (unitary_mul_image_eq_of_finiteConjugation S hS hc (W i)).2
    change a * (W i : H →L[ℂ] H) ∈ (S : Set (H →L[ℂ] H))
    rw [← heq]
    exact ⟨a, ha, rfl⟩

section SingletonTarget

variable {A : Type u} [NonUnitalCStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

/-- Starting at the specified algebra, the same faithful small GNS image has
unitary image equalities and arbitrary two-sided multiplier inclusions.
The witness includes the same literal preimage homeomorphism; faithfulness
and full normality are derived, not additional inputs. -/
theorem exists_faithful_image_unitary_invariant_of_singleton
    (hsingle : ∃ q : IrreducibleSpectrum A, ∀ r : IrreducibleSpectrum A, r = q)
    (hproperty : ∃ I : NormedSpace.GeometricStructureSpace ℂ A,
      ((NormedSpace.geometricStructureClosure ℂ A).subspace
        ((NormedSpace.geometricStructureClosure ℂ A).component I)).HasContinuousFiniteConjugation
          (ClosureCat.IsCStarRealizable.{u, max u v})) :
    ∃ phi : NonUnitalPureState A,
      Function.Injective phi.gnsRepresentation ∧
      normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation) = Set.univ ∧
      ∃ r : ClosureSpace.Homeomorph
          ((NormedSpace.geometricStructureClosure ℂ (NonUnitalStarAlgHom.range phi.gnsRepresentation)).subspace
            (normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation)))
          (NormedSpace.geometricStructureClosure ℂ A),
        (∀ J : normalPart (NonUnitalStarAlgHom.range phi.gnsRepresentation),
          (r.toEquiv J).val = (NonUnitalStarAlgHom.rangeRestrict phi.gnsRepresentation) ⁻¹' J.val.val) ∧
        (∀ W : unitary (phi.GNS →L[ℂ] phi.GNS),
          (fun a : phi.GNS →L[ℂ] phi.GNS => (W : phi.GNS →L[ℂ] phi.GNS) * a) ''
              ((NonUnitalStarAlgHom.range phi.gnsRepresentation) : Set (phi.GNS →L[ℂ] phi.GNS)) =
            (NonUnitalStarAlgHom.range phi.gnsRepresentation) ∧
          (fun a : phi.GNS →L[ℂ] phi.GNS => a * (W : phi.GNS →L[ℂ] phi.GNS)) ''
              ((NonUnitalStarAlgHom.range phi.gnsRepresentation) : Set (phi.GNS →L[ℂ] phi.GNS)) =
            (NonUnitalStarAlgHom.range phi.gnsRepresentation)) ∧
        (∀ (b a : phi.GNS →L[ℂ] phi.GNS), a ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation) →
          b * a ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation) ∧ a * b ∈ (NonUnitalStarAlgHom.range phi.gnsRepresentation)) := by
  obtain ⟨phi, hfaith, hnormal, hcomponents, r, hr, hiff⟩ :=
    exists_singleton_normalPart_finiteConjugation_model.{u, v} hsingle
  have hc := hiff.mp hproperty
  have hirr : NonUnitalCStarRepresentation.IsIrreducible (NonUnitalStarSubalgebraClass.subtype (NonUnitalStarAlgHom.range phi.gnsRepresentation)) :=
    (NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff phi.gnsRepresentation).mpr
      phi.isIrreducible_gnsRepresentation
  exact ⟨phi, hfaith, hnormal, r, hr,
    unitary_mul_image_eq_of_finiteConjugation (NonUnitalStarAlgHom.range phi.gnsRepresentation) hirr hc,
    fun b a ha => mul_mem_of_finiteConjugation (NonUnitalStarAlgHom.range phi.gnsRepresentation) hirr hc b ha⟩

end SingletonTarget
end MathlibAnnex.Analysis.CStarAlgebra
