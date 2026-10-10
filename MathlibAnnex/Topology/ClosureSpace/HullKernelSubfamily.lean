/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.HullKernelPreimage

/-!
# Intrinsic hull-kernel closure on a subfamily

A subfamily need not be closed in the ambient hull-kernel space. Its intrinsic
closure is exactly the subspace closure. All intersections are intersections
of sets, including the empty intersection. The preimage corollary only uses
surjectivity of the ambient function, never injectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ClosureSpace
namespace HullKernel

variable {X : Type u} {Y : Type v} {F G : Set (Set X)}

/-- The members of a subfamily, viewed as points of the ambient family. -/
def subfamily (F G : Set (Set X)) : Set F := {I | I.val ∈ G}

/-- The inclusion sends a set to the very same set in the ambient family. -/
def inclusionMap (hGF : G ⊆ F) : G → F := fun I => ⟨I.val, hGF I.property⟩

@[simp]
theorem inclusionMap_val (hGF : G ⊆ F) (I : G) :
    (inclusionMap hGF I).val = I.val := rfl

/-- Restricting the codomain of inclusion gives a bijection, with explicit inverse. -/
def subfamilyEquiv (hGF : G ⊆ F) : G ≃ subfamily F G where
  toFun I := ⟨inclusionMap hGF I, I.property⟩
  invFun I := ⟨I.val.val, I.property⟩
  left_inv I := by cases I; rfl
  right_inv I := by rcases I with ⟨⟨I, hI⟩, hIG⟩; rfl

@[simp]
theorem subfamilyEquiv_val (hGF : G ⊆ F) (I : G) :
    (subfamilyEquiv hGF I).val = inclusionMap hGF I := rfl

@[simp]
theorem subfamilyEquiv_symm_val (hGF : G ⊆ F) (I : subfamily F G) :
    ((subfamilyEquiv hGF).symm I).val = I.val.val := rfl

/-- The intersection of any selected subfamily is unchanged by inclusion. -/
theorem kernel_image_inclusionMap (hGF : G ⊆ F) (S : Set G) :
    kernel F (inclusionMap hGF '' S) = kernel G S := by
  ext x
  constructor
  · intro hx I hI
    exact hx (inclusionMap hGF I) ⟨I, hI, rfl⟩
  · intro hx I hI
    obtain ⟨J, hJ, rfl⟩ := hI
    exact hx J hJ

/-- In particular, the empty intersection remains the whole ambient set. -/
@[simp]
theorem kernel_image_inclusionMap_empty (hGF : G ⊆ F) :
    kernel F (inclusionMap hGF '' ∅) = Set.univ := by
  rw [kernel_image_inclusionMap, kernel_empty]

/-- Membership in the intrinsic closure is ambient closure membership after inclusion. -/
theorem inclusionMap_mem_closure_iff (hGF : G ⊆ F) (hF : Set.univ ∉ F)
    (S : Set G) (I : G) :
    inclusionMap hGF I ∈ (space F hF).closure (inclusionMap hGF '' S) ↔
      I ∈ (space G (fun h => hF (hGF h))).closure S := by
  change kernel F (inclusionMap hGF '' S) ⊆ I.val ↔ kernel G S ⊆ I.val
  rw [kernel_image_inclusionMap]

/-- The exact ambient-image formula; the intersection cannot in general be omitted. -/
theorem image_closure_inclusionMap (hGF : G ⊆ F) (hF : Set.univ ∉ F) (S : Set G) :
    inclusionMap hGF '' (space G (fun h => hF (hGF h))).closure S =
      subfamily F G ∩ (space F hF).closure (inclusionMap hGF '' S) := by
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    exact ⟨J.property, (inclusionMap_mem_closure_iff hGF hF S J).2 hJ⟩
  · rintro ⟨hIG, hI⟩
    let J : G := ⟨I.val, hIG⟩
    have hJI : inclusionMap hGF J = I := Subtype.ext rfl
    refine ⟨J, (inclusionMap_mem_closure_iff hGF hF S J).1 ?_, hJI⟩
    rwa [hJI]

/-- The subtype equivalence transports every intrinsic closure to the subspace closure. -/
theorem image_closure_subfamilyEquiv (hGF : G ⊆ F) (hF : Set.univ ∉ F)
    (S : Set G) :
    subfamilyEquiv hGF '' (space G (fun h => hF (hGF h))).closure S =
      ((space F hF).subspace (subfamily F G)).closure (subfamilyEquiv hGF '' S) := by
  have hi : (Subtype.val : subfamily F G → F) '' (subfamilyEquiv hGF '' S) =
      inclusionMap hGF '' S := by
    rw [Set.image_image]
    rfl
  ext I
  constructor
  · rintro ⟨J, hJ, rfl⟩
    change inclusionMap hGF J ∈ (space F hF).closure
      ((Subtype.val : subfamily F G → F) '' (subfamilyEquiv hGF '' S))
    rw [hi]
    exact (inclusionMap_mem_closure_iff hGF hF S J).2 hJ
  · intro hI
    let J := (subfamilyEquiv hGF).symm I
    refine ⟨J, ?_, (subfamilyEquiv hGF).apply_symm_apply I⟩
    apply (inclusionMap_mem_closure_iff hGF hF S J).1
    have hJI : inclusionMap hGF J = I.val := Subtype.ext rfl
    change I.val ∈ (space F hF).closure
      ((Subtype.val : subfamily F G → F) '' (subfamilyEquiv hGF '' S)) at hI
    rw [hi] at hI
    rwa [hJI]

/-- Intrinsic hull-kernel closure agrees with the actual ambient subspace closure. -/
def homeomorphSubfamily (hGF : G ⊆ F) (hF : Set.univ ∉ F) :
    Homeomorph (space G (fun h => hF (hGF h)))
      ((space F hF).subspace (subfamily F G)) :=
  Homeomorph.ofImageClosure _ _ (subfamilyEquiv hGF)
    (image_closure_subfamilyEquiv hGF hF)

@[simp]
theorem homeomorphSubfamily_val (hGF : G ⊆ F) (hF : Set.univ ∉ F) (I : G) :
    ((homeomorphSubfamily hGF hF).toEquiv I).val.val = I.val := rfl

@[simp]
theorem homeomorphSubfamily_symm_val (hGF : G ⊆ F) (hF : Set.univ ∉ F)
    (I : subfamily F G) :
    ((homeomorphSubfamily hGF hF).toEquiv.symm I).val = I.val.val := rfl

/-- The actual inverse also preserves every closure, including the empty one. -/
theorem image_closure_homeomorphSubfamily_symm (hGF : G ⊆ F) (hF : Set.univ ∉ F)
    (S : Set (subfamily F G)) :
    (homeomorphSubfamily hGF hF).toEquiv.symm ''
        ((space F hF).subspace (subfamily F G)).closure S =
      (space G (fun h => hF (hGF h))).closure
        ((homeomorphSubfamily hGF hF).toEquiv.symm '' S) :=
  (homeomorphSubfamily hGF hF).symm.image_closure S

/-- Pull back a family by a surjection and realize it as an ambient subspace.
The containment hypothesis only identifies the target subfamily; any specific
C*-algebraic family identity remains a separate application theorem. -/
def homeomorphPreimageSubfamily (q : X → Y) (hq : Function.Surjective q)
    (H : Set (Set Y)) (hH : Set.univ ∉ H) (F : Set (Set X))
    (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F) :
    Homeomorph (space H hH) ((space F hF).subspace (subfamily F (preimageFamily q H))) :=
  (homeomorphPreimage q hq H hH).trans (homeomorphSubfamily hHF hF)

@[simp]
theorem homeomorphPreimageSubfamily_val (q : X → Y) (hq : Function.Surjective q)
    (H : Set (Set Y)) (hH : Set.univ ∉ H) (F : Set (Set X))
    (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F) (J : H) :
    ((homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv J).val.val =
      q ⁻¹' J.val := rfl

/-- Forward membership is precisely the preimage membership of the original set. -/
theorem mem_homeomorphPreimageSubfamily_iff (q : X → Y) (hq : Function.Surjective q)
    (H : Set (Set Y)) (hH : Set.univ ∉ H) (F : Set (Set X))
    (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F) (J : H) (x : X) :
    x ∈ ((homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv J).val.val ↔
      q x ∈ J.val := Iff.rfl

/-- The inverse recovers the original member through its preimage, not through
an assumed inverse of the possibly noninjective map `q`. -/
theorem homeomorphPreimageSubfamily_symm_preimage (q : X → Y)
    (hq : Function.Surjective q) (H : Set (Set Y)) (hH : Set.univ ∉ H)
    (F : Set (Set X)) (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F)
    (I : subfamily F (preimageFamily q H)) :
    q ⁻¹' ((homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv.symm I).val =
      I.val.val :=
  preimageEquiv_symm_val q hq H ((subfamilyEquiv hHF).symm I)

/-- Exact image of any closure in the ambient-subtype formulation. -/
theorem image_closure_homeomorphPreimageSubfamily (q : X → Y)
    (hq : Function.Surjective q) (H : Set (Set Y)) (hH : Set.univ ∉ H)
    (F : Set (Set X)) (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F) (S : Set H) :
    (homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv '' (space H hH).closure S =
      ((space F hF).subspace (subfamily F (preimageFamily q H))).closure
        ((homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv '' S) :=
  (homeomorphPreimageSubfamily q hq H hH F hF hHF).image_closure S

/-- The inverse ambient-subtype map preserves all closures too. -/
theorem image_closure_homeomorphPreimageSubfamily_symm (q : X → Y)
    (hq : Function.Surjective q) (H : Set (Set Y)) (hH : Set.univ ∉ H)
    (F : Set (Set X)) (hF : Set.univ ∉ F) (hHF : preimageFamily q H ⊆ F)
    (S : Set (subfamily F (preimageFamily q H))) :
    (homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv.symm ''
        ((space F hF).subspace (subfamily F (preimageFamily q H))).closure S =
      (space H hH).closure
        ((homeomorphPreimageSubfamily q hq H hH F hF hHF).toEquiv.symm '' S) :=
  (homeomorphPreimageSubfamily q hq H hH F hF hHF).symm.image_closure S

end HullKernel
end ClosureSpace
