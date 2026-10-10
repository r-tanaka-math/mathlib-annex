/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.FilterPresentation
public import MathlibAnnex.Topology.ClosureSpace.HullKernelMap

/-!
# Actual geometric-structure maps induced by orthogonality preservers

A bijection preserving and reflecting Birkhoff-James orthogonality transports
order filters, their maximal elements, and their intersection kernels. The
face/filter comparison proves that the image is a point of the original
geometric structure space. This supplies the actual incidence equivalence
required by the previously frozen hull-kernel homeomorphism construction.
The scalar fields of the two spaces may differ; no linearity is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v w z

namespace NormedSpace

variable (𝕜 : Type v) (𝕝 : Type z) [RCLike 𝕜] [RCLike 𝕝]
variable {E : Type u} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕝 F]
variable (e : E ≃ F)
variable (h : ∀ x y : E, BirkhoffJamesOrthogonal 𝕝 (e x) (e y) ↔
  BirkhoffJamesOrthogonal 𝕜 x y)
include h

theorem birkhoffJamesOrthogonal_symm_equiv (x y : F) :
    BirkhoffJamesOrthogonal 𝕜 (e.symm x) (e.symm y) ↔
      BirkhoffJamesOrthogonal 𝕝 x y := by
  simpa only [e.apply_symm_apply] using (h (e.symm x) (e.symm y)).symm

/-- An orthogonality equivalence preserves the distinguished zero vector. -/
theorem map_zero_of_birkhoffJamesOrthogonal_iff : e (0 : E) = 0 :=
  (birkhoffJamesOrthogonal_self_iff (e (0 : E))).mp
    ((h 0 0).mpr (birkhoffJamesOrthogonal_zero_left 0))

theorem birkhoffJamesOrthogonalSet_subset_equiv_iff (x y : E) :
    birkhoffJamesOrthogonalSet 𝕝 (e x) ⊆ birkhoffJamesOrthogonalSet 𝕝 (e y) ↔
      birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y := by
  constructor
  · intro hxy a ha
    exact (h y a).mp (hxy ((h x a).mpr ha))
  · intro hxy b hb
    obtain ⟨a, rfl⟩ := e.surjective b
    exact (h y a).mpr (hxy ((h x a).mp hb))

/-- The image of an order filter is an order filter for the other space's
orthogonality preorder. -/
theorem IsBirkhoffJamesFilter.image_equiv {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U) :
    IsBirkhoffJamesFilter 𝕝 (e '' U) := by
  apply (isBirkhoffJamesFilter_iff 𝕝 _).mpr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hU.nonempty 𝕜
    exact ⟨e x, x, hx, rfl⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    obtain ⟨q, hq, hqx, hqy⟩ := hU.directed 𝕜 hx hy
    exact ⟨e q, ⟨q, hq, rfl⟩,
      (birkhoffJamesOrthogonalSet_subset_equiv_iff 𝕜 𝕝 e h q x).mpr hqx,
      (birkhoffJamesOrthogonalSet_subset_equiv_iff 𝕜 𝕝 e h q y).mpr hqy⟩
  · rintro a b hab ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := e.surjective b
    exact ⟨y, hU.mem_of_subset 𝕜
      ((birkhoffJamesOrthogonalSet_subset_equiv_iff 𝕜 𝕝 e h x y).mp hab) hx, rfl⟩

theorem IsMaximalBirkhoffJamesFilter.image_equiv {U : Set E}
    (hU : IsMaximalBirkhoffJamesFilter 𝕜 U) : IsMaximalBirkhoffJamesFilter 𝕝 (e '' U) := by
  refine ⟨hU.1.image_equiv 𝕜 𝕝 e h, ?_⟩
  intro V hV hUV y hy
  have hback : IsBirkhoffJamesFilter 𝕜 (e.symm '' V) :=
    hV.image_equiv 𝕝 𝕜 e.symm (birkhoffJamesOrthogonal_symm_equiv 𝕜 𝕝 e h)
  have hsub : U ⊆ e.symm '' V := by
    intro x hx
    exact ⟨e x, hUV ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  exact ⟨e.symm y, hU.2 hback hsub ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- Exact transport of intersection kernels; no continuity or linearity is
needed before the hull-kernel closure is introduced. -/
theorem image_birkhoffJamesKernel (U : Set E) :
    e '' birkhoffJamesKernel 𝕜 U = birkhoffJamesKernel 𝕝 (e '' U) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ a ⟨b, hb, rfl⟩
    exact (h b x).mpr (hx b hb)
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, fun a ha => (h a x).mp (hy (e a) ⟨a, ha, rfl⟩), rfl⟩

/-- The image is in the original face-defined geometric-structure family,
not merely in a newly postulated family of kernels. -/
theorem image_mem_geometricStructureFamily {I : Set E} (hI : I ∈ geometricStructureFamily 𝕜 E) :
    e '' I ∈ geometricStructureFamily 𝕝 F := by
  classical
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    rw [geometricStructureFamily_eq_empty_of_subsingleton 𝕜 E] at hI
    exact hI.elim
  · letI := hE
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    letI : Nontrivial F := ⟨⟨e x, e 0, fun heq => hx (e.injective heq)⟩⟩
    obtain ⟨U, hU, hUI⟩ :=
      (mem_geometricStructureFamily_iff_exists_maximal_filter 𝕜 E I).mp hI
    apply (mem_geometricStructureFamily_iff_exists_maximal_filter 𝕝 F (e '' I)).mpr
    refine ⟨e '' U, hU.image_equiv 𝕜 𝕝 e h, ?_⟩
    rw [← image_birkhoffJamesKernel 𝕜 𝕝 e h, hUI]

/-- The actual induced equivalence on face-defined geometric structure spaces. -/
def geometricStructureEquivOfBirkhoffJames :
    GeometricStructureSpace 𝕜 E ≃ GeometricStructureSpace 𝕝 F where
  toFun I := ⟨e '' I.val, image_mem_geometricStructureFamily 𝕜 𝕝 e h I.property⟩
  invFun J := ⟨e.symm '' J.val, image_mem_geometricStructureFamily 𝕝 𝕜 e.symm
    (birkhoffJamesOrthogonal_symm_equiv 𝕜 𝕝 e h) J.property⟩
  left_inv I := by
    apply Subtype.ext
    simp only [image_image, Function.comp_def, e.symm_apply_apply]
    change id '' I.val = I.val
    exact Set.image_id I.val
  right_inv J := by
    apply Subtype.ext
    simp only [image_image, Function.comp_def, e.apply_symm_apply]
    change id '' J.val = J.val
    exact Set.image_id J.val

/-- Incidence is transported in both directions by the explicitly constructed
map; this is the hypothesis consumed by `homeomorphOfMemIff`. -/
theorem mem_geometricStructureEquivOfBirkhoffJames (I : GeometricStructureSpace 𝕜 E) (x : E) :
    e x ∈ (geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 e h I).val ↔ x ∈ I.val := by
  constructor
  · rintro ⟨y, hy, heq⟩
    exact e.injective heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- An orthogonality equivalence induces a homeomorphism for the already
constructed hull-kernel closures. Both zero and nonzero spaces are covered. -/
def geometricStructureHomeomorphOfBirkhoffJames :
    ClosureSpace.Homeomorph (geometricStructureClosure 𝕜 E) (geometricStructureClosure 𝕝 F) :=
  ClosureSpace.HullKernel.homeomorphOfMemIff
    (univ_notMem_geometricStructureFamily 𝕜 E) (univ_notMem_geometricStructureFamily 𝕝 F)
    e (geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 e h)
    (mem_geometricStructureEquivOfBirkhoffJames 𝕜 𝕝 e h)

end NormedSpace
