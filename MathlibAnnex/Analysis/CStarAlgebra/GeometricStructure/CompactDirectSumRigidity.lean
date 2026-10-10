/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.GeometricStructure.CompactDirectSumComponents
import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.EmptyModelEquiv

/-!
# GSS rigidity for two given compact-operator c₀-sum models

For two explicitly supplied compact-operator c₀-sum models, a specified full
GSS homeomorphism determines the index equivalence and genuine complex-linear
Hilbert-space isometry equivalences of the matched fibers.  The previously
constructed dependent c₀ assembly then gives an actual non-unital C-star
algebra equivalence of the original algebras.

The resulting star equivalence is not asserted to induce the supplied
nonlinear GSS homeomorphism.  This is the restricted, complete assembly for two
given actual models; it does not supply the separate compact-subalgebra-to-c₀
model-existence theorem required for the unrestricted Paper 8.12 statement.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open InnerProductSpace
open scoped CStarAlgebra Cardinal

namespace MathlibAnnex.Analysis.CStarAlgebra

universe uA uB uι uκ uH uK uI uJ

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {ι : Type uι} {κ : Type uκ}
variable (H : ι → Type uH) (K : κ → Type uK)
variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
variable [∀ i, CompleteSpace (H i)] [∀ i, Nontrivial (H i)]
variable [∀ j, NormedAddCommGroup (K j)] [∀ j, InnerProductSpace ℂ (K j)]
variable [∀ j, CompleteSpace (K j)] [∀ j, Nontrivial (K j)]

local instance : PartialOrder (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (CompactOperatorC0Sum H) :=
  _root_.CStarAlgebra.spectralOrderedRing _
local instance : PartialOrder (CompactOperatorC0Sum K) :=
  _root_.CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (CompactOperatorC0Sum K) :=
  _root_.CStarAlgebra.spectralOrderedRing _

section NonemptyIndices

variable [Nonempty ι] [Nonempty κ]

local instance : Nontrivial (CompactOperatorC0Sum H) := by
  classical
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  let a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H i) := ⟨rankOne ℂ x x, isCompactOperator_rankOne x x⟩
  have ha : a ≠ 0 := by
    intro h
    apply rankOne_ne_zero (𝕜 := ℂ) hx hx
    exact congrArg Subtype.val h
  refine ⟨⟨C0DirectSum.single (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i a, 0, ?_⟩⟩
  intro h
  have h' := congrArg (C0DirectSum.eval (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i) h
  simp only [C0DirectSum.eval_single_same, map_zero] at h'
  exact ha h'

local instance : Nontrivial (CompactOperatorC0Sum K) := by
  classical
  let i : κ := Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨x, hx⟩ := exists_ne (0 : K i)
  let a : ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K i) := ⟨rankOne ℂ x x, isCompactOperator_rankOne x x⟩
  have ha : a ≠ 0 := by
    intro h
    apply rankOne_ne_zero (𝕜 := ℂ) hx hx
    exact congrArg Subtype.val h
  refine ⟨⟨C0DirectSum.single (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j)) i a, 0, ?_⟩⟩
  intro h
  have h' := congrArg (C0DirectSum.eval (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j)) i) h
  simp only [C0DirectSum.eval_single_same, map_zero] at h'
  exact ha h'

variable (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
variable (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
variable (F : ClosureSpace.Homeomorph
  (NormedSpace.geometricStructureClosure ℂ A)
  (NormedSpace.geometricStructureClosure ℂ B))

/-- The index equivalence recovered from the specified model homeomorphism. -/
def compactDirectSumRigidityIndexEquiv : ι ≃ κ :=
  CompactOperatorC0Sum.indexEquivOfGeometricStructure H K
    (compactDirectSumModelGeometricStructureHomeomorph H K EA EB F)

@[simp]
theorem compactDirectSumRigidityIndexEquiv_apply (i : ι) :
    compactDirectSumRigidityIndexEquiv H K EA EB F i =
      (CompactOperatorC0Sum.coordinateSpectrumEquiv K).symm
        ((irreducibleSpectrumHomeomorphOfGeometricStructure
          (compactDirectSumModelGeometricStructureHomeomorph H K EA EB F)).toEquiv
            (CompactOperatorC0Sum.coordinateSpectrumEquiv H i)) := rfl

/-- The specified model homeomorphism gives genuine Hilbert-basis cardinal
agreement on every forced coordinate pair. -/
theorem hilbertBasis_lift_mk_eq_compactDirectSumRigidity
    {α : Type uI} {β : Type uJ} (i : ι)
    (b : HilbertBasis α ℂ (H i))
    (c : HilbertBasis β ℂ
      (K (compactDirectSumRigidityIndexEquiv H K EA EB F i))) :
    Cardinal.lift.{uJ} (#α) = Cardinal.lift.{uI} (#β) :=
  CompactOperatorC0Sum.hilbertBasis_lift_mk_eq_of_matched_coordinate H K
    (compactDirectSumModelGeometricStructureHomeomorph H K EA EB F) i b c

/-- The actual complex-linear Hilbert equivalence attached to each forced
coordinate correspondence. -/
def compactDirectSumRigidityFiberEquiv (i : ι) :
    H i ≃ₗᵢ[ℂ] K (compactDirectSumRigidityIndexEquiv H K EA EB F i) :=
  CompactOperatorC0Sum.fiberLinearIsometryEquivOfGeometricStructure H K
    (compactDirectSumModelGeometricStructureHomeomorph H K EA EB F) i

/-- The star equivalence assembled from the index and fiber data forced by the
specified GSS homeomorphism. -/
def compactDirectSumRigidityStarAlgEquiv : A ≃⋆ₐ[ℂ] B :=
  compactDirectSumModelStarAlgEquiv H K EA EB
    (compactDirectSumRigidityIndexEquiv H K EA EB F)
    (compactDirectSumRigidityFiberEquiv H K EA EB F)

@[simp]
theorem compactDirectSumRigidityStarAlgEquiv_apply (a : A) :
    compactDirectSumRigidityStarAlgEquiv H K EA EB F a =
      EB.symm
        (CompactOperatorC0Sum.equiv H K
          (compactDirectSumRigidityIndexEquiv H K EA EB F)
          (compactDirectSumRigidityFiberEquiv H K EA EB F) (EA a)) := rfl

@[simp]
theorem compactDirectSumRigidityStarAlgEquiv_symm_apply (b : B) :
    (compactDirectSumRigidityStarAlgEquiv H K EA EB F).symm b =
      EA.symm
        ((CompactOperatorC0Sum.equiv H K
          (compactDirectSumRigidityIndexEquiv H K EA EB F)
          (compactDirectSumRigidityFiberEquiv H K EA EB F)).symm (EB b)) := rfl

/-- Forward coordinate formula in the two original models. -/
@[simp]
theorem eval_compactDirectSumRigidityStarAlgEquiv
    (a : A) (i : ι) :
    C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j))
        (compactDirectSumRigidityIndexEquiv H K EA EB F i)
        (EB (compactDirectSumRigidityStarAlgEquiv H K EA EB F a)) =
      (compactDirectSumRigidityFiberEquiv H K EA EB F i).compactOperatorStarAlgEquiv
        (C0DirectSum.eval
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j))
          i (EA a)) := by
  exact eval_compactDirectSumModelStarAlgEquiv H K EA EB
    (compactDirectSumRigidityIndexEquiv H K EA EB F)
    (compactDirectSumRigidityFiberEquiv H K EA EB F) a i

set_option maxHeartbeats 8000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse coordinate formula in the two original models. -/
@[simp]
theorem eval_compactDirectSumRigidityStarAlgEquiv_symm
    (b : B) (i : ι) :
    C0DirectSum.eval
        (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (H j)) i
        (EA ((compactDirectSumRigidityStarAlgEquiv H K EA EB F).symm b)) =
      ((compactDirectSumRigidityFiberEquiv H K EA EB F i).compactOperatorStarAlgEquiv).symm
        (C0DirectSum.eval
          (fun j => ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K j))
          (compactDirectSumRigidityIndexEquiv H K EA EB F i) (EB b)) := by
  rw [compactDirectSumRigidityStarAlgEquiv_symm_apply, EA.apply_symm_apply]
  exact CompactOperatorC0Sum.eval_equiv_symm_apply H K
    (compactDirectSumRigidityIndexEquiv H K EA EB F)
    (compactDirectSumRigidityFiberEquiv H K EA EB F) (EB b) i

/-- The assembled equivalence preserves the original C-star norms. -/
@[simp]
theorem norm_compactDirectSumRigidityStarAlgEquiv (a : A) :
    ‖compactDirectSumRigidityStarAlgEquiv H K EA EB F a‖ = ‖a‖ := by
  simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, map_zero, dist_zero_right] using
    (NonUnitalStarAlgHom.isometry
      (compactDirectSumRigidityStarAlgEquiv H K EA EB F).toNonUnitalStarAlgHom
      (compactDirectSumRigidityStarAlgEquiv H K EA EB F).injective).dist_eq a 0

include H K EA EB F in
/-- Existence endpoint for the nonempty-index range. -/
theorem nonempty_starAlgEquiv_of_compact_direct_sum_models_of_geometricStructure_homeomorph_of_nonempty :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
  ⟨compactDirectSumRigidityStarAlgEquiv H K EA EB F⟩

end NonemptyIndices



section AllIndices

variable (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
variable (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)
variable (F : ClosureSpace.Homeomorph
  (NormedSpace.geometricStructureClosure ℂ A)
  (NormedSpace.geometricStructureClosure ℂ B))

include H K EA EB F in
/-- An empty source index and a nonempty target index are incompatible with a
GSS homeomorphism between the two specified compact c₀ models. -/
theorem not_nonempty_target_of_isEmpty_source
    [IsEmpty ι] [Nonempty κ] : False := by
  letI : Subsingleton (CompactOperatorC0Sum H) := inferInstance
  letI : IsEmpty
      (NormedSpace.GeometricStructureSpace ℂ (CompactOperatorC0Sum H)) :=
    NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ
      (CompactOperatorC0Sum H)
  let j : κ := Classical.choice (inferInstance : Nonempty κ)
  obtain ⟨y, hy⟩ := exists_ne (0 : K j)
  let J := CompactOperatorC0Sum.coordinateCoefficientPoint K j y hy
  exact isEmptyElim
    ((compactDirectSumModelGeometricStructureHomeomorph H K EA EB F).toEquiv.symm J)

include H K EA EB F in
/-- A nonempty source index and an empty target index are incompatible with a
GSS homeomorphism between the two specified compact c₀ models. -/
theorem not_isEmpty_target_of_nonempty_source
    [Nonempty ι] [IsEmpty κ] : False := by
  letI : Subsingleton (CompactOperatorC0Sum K) := inferInstance
  letI : IsEmpty
      (NormedSpace.GeometricStructureSpace ℂ (CompactOperatorC0Sum K)) :=
    NormedSpace.isEmpty_geometricStructureSpace_of_subsingleton ℂ
      (CompactOperatorC0Sum K)
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨x, hx⟩ := exists_ne (0 : H i)
  let I := CompactOperatorC0Sum.coordinateCoefficientPoint H i x hx
  exact isEmptyElim
    ((compactDirectSumModelGeometricStructureHomeomorph H K EA EB F).toEquiv I)

include H K EA EB F in
/-- For arbitrary index types, two specified compact-operator c₀ models with
homeomorphic GSSs are star equivalent.  The nonempty/nonempty branch uses the
spectrally forced index and fiber equivalences.  The empty/empty branch is
algebraic, and the two mixed branches are impossible. -/
theorem nonempty_starAlgEquiv_of_compact_direct_sum_models_of_geometricStructure_homeomorph :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI : IsEmpty ι := hι
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · letI : IsEmpty κ := hκ
      exact nonempty_starAlgEquiv_of_empty_compact_direct_sum_models H K EA EB
    · letI : Nonempty κ := hκ
      exact (not_nonempty_target_of_isEmpty_source H K EA EB F).elim
  · letI : Nonempty ι := hι
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · letI : IsEmpty κ := hκ
      exact (not_isEmpty_target_of_nonempty_source H K EA EB F).elim
    · letI : Nonempty κ := hκ
      exact
        nonempty_starAlgEquiv_of_compact_direct_sum_models_of_geometricStructure_homeomorph_of_nonempty
          H K EA EB F

end AllIndices

end MathlibAnnex.Analysis.CStarAlgebra
