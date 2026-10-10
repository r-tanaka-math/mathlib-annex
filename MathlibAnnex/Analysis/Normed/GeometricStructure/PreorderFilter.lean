/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/
module

public import MathlibAnnex.Analysis.Normed.GeometricStructure.AbsoluteSupport
public import Mathlib.Order.PFilter
public import Mathlib.Order.Zorn

/-!
# Filters of the orthogonality preorder

`IsBirkhoffJamesFilter` specializes the existing `Order.IsPFilter`. These are
subsets of the vector space, not collections of subsets as in `Filter E`.
Maximal means maximal among all these nonempty order filters, not maximal
proper lattice filters. No order instance is installed globally on `E`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set

universe u v

namespace NormedSpace

variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The existing order-filter predicate for the orthogonality preorder. -/
def IsBirkhoffJamesFilter (U : Set E) : Prop :=
  @Order.IsPFilter E (birkhoffJamesPreorder 𝕜) U

/-- Maximality is among all nonempty order filters. -/
def IsMaximalBirkhoffJamesFilter (U : Set E) : Prop :=
  Maximal (IsBirkhoffJamesFilter 𝕜) U

/-- Explicit properties of the specialized order filter. -/
theorem isBirkhoffJamesFilter_iff (U : Set E) :
    IsBirkhoffJamesFilter 𝕜 U ↔ U.Nonempty ∧
      (∀ x ∈ U, ∀ y ∈ U, ∃ z ∈ U,
        birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
        birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y) ∧
      (∀ x y : E, birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y →
        x ∈ U → y ∈ U) := by
  letI : Preorder E := birkhoffJamesPreorder 𝕜
  constructor
  · intro h
    exact ⟨h.Nonempty, h.Directed, fun _ _ hxy hx => h.IsLowerSet hxy hx⟩
  · rintro ⟨hne, hdir, hup⟩
    exact @Order.IsPFilter.of_def E (birkhoffJamesPreorder 𝕜) U hne hdir
      (fun {x y} hxy hx => hup x y hxy hx)

theorem IsBirkhoffJamesFilter.nonempty {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U) :
    U.Nonempty := (isBirkhoffJamesFilter_iff 𝕜 U).mp hU |>.1

theorem IsBirkhoffJamesFilter.directed {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ z ∈ U, birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y :=
  ((isBirkhoffJamesFilter_iff 𝕜 U).mp hU).2.1 x hx y hy

theorem IsBirkhoffJamesFilter.mem_of_subset {U : Set E}
    (hU : IsBirkhoffJamesFilter 𝕜 U) {x y : E}
    (hxy : birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y)
    (hx : x ∈ U) : y ∈ U :=
  ((isBirkhoffJamesFilter_iff 𝕜 U).mp hU).2.2 x y hxy hx

theorem IsBirkhoffJamesFilter.zero_mem {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U) :
    (0 : E) ∈ U := by
  obtain ⟨x, hx⟩ := hU.nonempty 𝕜
  apply hU.mem_of_subset 𝕜 (x := x) _ hx
  rw [birkhoffJamesOrthogonalSet_zero]
  exact subset_univ _

theorem IsBirkhoffJamesFilter.smul_mem {U : Set E} (hU : IsBirkhoffJamesFilter 𝕜 U)
    {x : E} (hx : x ∈ U) (a : 𝕜) : a • x ∈ U :=
  hU.mem_of_subset 𝕜 (birkhoffJamesOrthogonalSet_subset_smul 𝕜 x a) hx

/-- Upward closure in the explicit orthogonality preorder. -/
def birkhoffJamesUpperClosure (D : Set E) : Set E :=
  {y | ∃ x ∈ D, birkhoffJamesOrthogonalSet 𝕜 x ⊆ birkhoffJamesOrthogonalSet 𝕜 y}

theorem subset_birkhoffJamesUpperClosure (D : Set E) :
    D ⊆ birkhoffJamesUpperClosure 𝕜 D := fun x hx => ⟨x, hx, Subset.rfl⟩

theorem isBirkhoffJamesFilter_upperClosure {D : Set E} (hne : D.Nonempty)
    (hdir : ∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D,
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y) :
    IsBirkhoffJamesFilter 𝕜 (birkhoffJamesUpperClosure 𝕜 D) := by
  apply (isBirkhoffJamesFilter_iff 𝕜 _).mpr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, subset_birkhoffJamesUpperClosure 𝕜 D hx⟩
  · rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hby⟩
    obtain ⟨z, hz, hza, hzb⟩ := hdir a ha b hb
    exact ⟨z, subset_birkhoffJamesUpperClosure 𝕜 D hz, hza.trans hax, hzb.trans hby⟩
  · rintro x y hxy ⟨a, ha, hax⟩
    exact ⟨a, ha, hax.trans hxy⟩

/-- Every order filter is contained in a maximal one. Increasing chain unions
satisfy the three order-filter properties; no compactness is used here. -/
theorem IsBirkhoffJamesFilter.exists_maximal {U : Set E}
    (hU : IsBirkhoffJamesFilter 𝕜 U) :
    ∃ V : Set E, U ⊆ V ∧ IsMaximalBirkhoffJamesFilter 𝕜 V := by
  apply zorn_subset_nonempty {V : Set E | IsBirkhoffJamesFilter 𝕜 V} _ U hU
  intro c hc hchain hcne
  refine ⟨⋃₀ c, ?_, fun V hV => subset_sUnion_of_mem hV⟩
  apply (isBirkhoffJamesFilter_iff 𝕜 _).mpr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨V, hV⟩ := hcne
    obtain ⟨x, hx⟩ := (hc hV).nonempty 𝕜
    exact ⟨x, mem_sUnion_of_mem hx hV⟩
  · rintro x ⟨V, hV, hx⟩ y ⟨W, hW, hy⟩
    rcases hchain.total hV hW with hVW | hWV
    · obtain ⟨z, hz, hzx, hzy⟩ := (hc hW).directed 𝕜 (hVW hx) hy
      exact ⟨z, mem_sUnion_of_mem hz hW, hzx, hzy⟩
    · obtain ⟨z, hz, hzx, hzy⟩ := (hc hV).directed 𝕜 hx (hWV hy)
      exact ⟨z, mem_sUnion_of_mem hz hV, hzx, hzy⟩
  · rintro x y hxy ⟨V, hV, hx⟩
    exact mem_sUnion_of_mem ((hc hV).mem_of_subset 𝕜 hxy hx) hV

/-- The maximal-filter extension theorem starts from any nonempty downward
directed subset, not only from a subset already known to be upward closed. -/
theorem exists_isMaximalBirkhoffJamesFilter_of_directed {D : Set E} (hne : D.Nonempty)
    (hdir : ∀ x ∈ D, ∀ y ∈ D, ∃ z ∈ D,
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 x ∧
      birkhoffJamesOrthogonalSet 𝕜 z ⊆ birkhoffJamesOrthogonalSet 𝕜 y) :
    ∃ U : Set E, D ⊆ U ∧ IsMaximalBirkhoffJamesFilter 𝕜 U := by
  obtain ⟨U, hDU, hU⟩ := (isBirkhoffJamesFilter_upperClosure 𝕜 hne hdir).exists_maximal 𝕜
  exact ⟨U, (subset_birkhoffJamesUpperClosure 𝕜 D).trans hDU, hU⟩

/-- The intersection of right orthogonality sets indexed by a subset. For a
maximal order filter this is the set denoted by `I_U` in the filter description. -/
def birkhoffJamesKernel (U : Set E) : Set E :=
  {y | ∀ x ∈ U, BirkhoffJamesOrthogonal 𝕜 x y}

@[simp]
theorem mem_birkhoffJamesKernel {U : Set E} {y : E} :
    y ∈ birkhoffJamesKernel 𝕜 U ↔ ∀ x ∈ U, BirkhoffJamesOrthogonal 𝕜 x y := Iff.rfl

theorem birkhoffJamesKernel_antitone : Antitone (birkhoffJamesKernel 𝕜 (E := E)) :=
  fun _ _ h _ hy x hx => hy x (h hx)

@[simp]
theorem zero_mem_birkhoffJamesKernel (U : Set E) : (0 : E) ∈ birkhoffJamesKernel 𝕜 U :=
  fun _ _ => birkhoffJamesOrthogonal_zero_right _

end NormedSpace
