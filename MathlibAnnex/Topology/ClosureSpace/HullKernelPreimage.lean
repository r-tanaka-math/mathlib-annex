/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Topology.ClosureSpace.HullKernel

/-!
# Hull-kernel families pulled back along a surjection

The ambient function need not be injective. Surjectivity reflects inclusion
of subsets and makes preimage injective on the family. The family map and its
inverse are constructed, and closure preservation is proved rather than
assumed. Intersections, including the empty intersection, are sets only.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace ClosureSpace
namespace HullKernel

variable {X : Type u} {Y : Type v}

/-- The actual family of preimages of members of `F`. -/
def preimageFamily (q : X → Y) (F : Set (Set Y)) : Set (Set X) :=
  (fun J : Set Y => q ⁻¹' J) '' F

/-- Preimage, with codomain the image family. -/
def preimageMap (q : X → Y) (F : Set (Set Y)) : F → preimageFamily q F :=
  fun J => ⟨q ⁻¹' J.val, ⟨J.val, J.property, rfl⟩⟩

@[simp]
theorem preimageMap_val (q : X → Y) (F : Set (Set Y)) (J : F) :
    (preimageMap q F J).val = q ⁻¹' J.val := rfl

/-- The map onto the preimage family is always surjective. -/
theorem preimageMap_surjective (q : X → Y) (F : Set (Set Y)) :
    Function.Surjective (preimageMap q F) := by
  rintro ⟨I, J, hJ, rfl⟩
  exact ⟨⟨J, hJ⟩, rfl⟩

/-- It is injective when the ambient map is surjective, not necessarily bijective. -/
theorem preimageMap_injective (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) : Function.Injective (preimageMap q F) := by
  intro I J h
  apply Subtype.ext
  ext y
  obtain ⟨x, rfl⟩ := hq y
  have hv := congrArg Subtype.val h
  change q ⁻¹' I.val = q ⁻¹' J.val at hv
  exact Set.ext_iff.mp hv x

/-- The bijection from a family to its actual preimage family. -/
def preimageEquiv (q : X → Y) (hq : Function.Surjective q) (F : Set (Set Y)) :
    F ≃ preimageFamily q F :=
  Equiv.ofBijective (preimageMap q F)
    ⟨preimageMap_injective q hq F, preimageMap_surjective q F⟩

@[simp]
theorem preimageEquiv_apply (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (J : F) :
    preimageEquiv q hq F J = preimageMap q F J := rfl

/-- The inverse recovers a set whose preimage is the given family member. -/
theorem preimageEquiv_symm_val (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (I : preimageFamily q F) :
    q ⁻¹' ((preimageEquiv q hq F).symm I).val = I.val :=
  congrArg Subtype.val ((preimageEquiv q hq F).apply_symm_apply I)

/-- Properness of all members is preserved by a surjective pullback. -/
theorem univ_notMem_preimageFamily (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (hF : Set.univ ∉ F) : Set.univ ∉ preimageFamily q F := by
  rintro ⟨J, hJ, h⟩
  change q ⁻¹' J = Set.univ at h
  apply hF
  have hJtop : J = Set.univ := by
    apply Set.eq_univ_iff_forall.2
    intro y
    obtain ⟨x, rfl⟩ := hq y
    have hx : x ∈ q ⁻¹' J := by rw [h]; trivial
    exact hx
  exact hJtop ▸ hJ

/-- Preimage commutes with the intersection selected by any set of family points. -/
theorem kernel_image_preimageMap (q : X → Y) (F : Set (Set Y)) (S : Set F) :
    kernel (preimageFamily q F) (preimageMap q F '' S) = q ⁻¹' kernel F S := by
  ext x
  constructor
  · intro hx I hI
    exact hx (preimageMap q F I) ⟨I, hI, rfl⟩
  · intro hx J hJ
    obtain ⟨I, hI, rfl⟩ := hJ
    exact hx I hI

/-- Hull membership is reflected because every ambient target point has a preimage. -/
theorem preimageMap_mem_hull_preimage_iff (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (A : Set Y) (J : F) :
    preimageMap q F J ∈ hull (preimageFamily q F) (q ⁻¹' A) ↔ J ∈ hull F A := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hq y
    exact h hy
  · intro h x hx
    exact h hx

/-- The image of every closure is exactly the closure of the image. -/
theorem image_closure_preimageMap (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (hF : Set.univ ∉ F) (S : Set F) :
    preimageMap q F '' (space F hF).closure S =
      (space (preimageFamily q F) (univ_notMem_preimageFamily q hq F hF)).closure
        (preimageMap q F '' S) := by
  ext I
  obtain ⟨J, rfl⟩ := preimageMap_surjective q F I
  constructor
  · rintro ⟨J', hJ', hJJ⟩
    have heq : J' = J := preimageMap_injective q hq F hJJ
    subst J'
    change kernel (preimageFamily q F) (preimageMap q F '' S) ⊆
      (preimageMap q F J).val
    rw [kernel_image_preimageMap]
    exact (preimageMap_mem_hull_preimage_iff q hq F (kernel F S) J).2 hJ'
  · intro hJ
    refine ⟨J, ?_, rfl⟩
    apply (preimageMap_mem_hull_preimage_iff q hq F (kernel F S) J).1
    change q ⁻¹' kernel F S ⊆ (preimageMap q F J).val
    rw [← kernel_image_preimageMap]
    exact hJ

/-- A surjective ambient map induces a homeomorphism of hull-kernel families. -/
def homeomorphPreimage (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (hF : Set.univ ∉ F) :
    Homeomorph (space F hF)
      (space (preimageFamily q F) (univ_notMem_preimageFamily q hq F hF)) :=
  Homeomorph.ofImageClosure _ _ (preimageEquiv q hq F)
    (image_closure_preimageMap q hq F hF)

/-- The homeomorphism has the required actual preimage formula on every set. -/
@[simp]
theorem homeomorphPreimage_val (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (hF : Set.univ ∉ F) (J : F) :
    ((homeomorphPreimage q hq F hF).toEquiv J).val = q ⁻¹' J.val := rfl

/-- The inverse preserves every closure too, including that of the empty set. -/
theorem image_closure_homeomorphPreimage_symm (q : X → Y) (hq : Function.Surjective q)
    (F : Set (Set Y)) (hF : Set.univ ∉ F) (S : Set (preimageFamily q F)) :
    (homeomorphPreimage q hq F hF).toEquiv.symm ''
      (space (preimageFamily q F) (univ_notMem_preimageFamily q hq F hF)).closure S =
        (space F hF).closure ((homeomorphPreimage q hq F hF).toEquiv.symm '' S) :=
  (homeomorphPreimage q hq F hF).symm.image_closure S

end HullKernel
end ClosureSpace
