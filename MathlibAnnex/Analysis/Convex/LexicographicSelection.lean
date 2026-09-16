import Mathlib

/-!
# Lexicographic selection from compact generators

A nonempty compact set is repeatedly cut down to the maximizers of a finite
ordered dictionary of continuous linear functionals.  Equality of the original
convex hulls is preserved at every stage.  If the dictionary separates points,
the final compact slices are singletons, and the two singletons coincide.

The public finite-coordinate theorem keeps the original `Good` conclusion:
the common point belongs to both raw generator sets and satisfies every property
known on the first target-side support slice.
-/

noncomputable section

open Set
open TopologicalSpace

namespace MathlibAnnex

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace NonemptyCompacts

/-- A selected maximizer of a continuous linear functional on a nonempty compact set. -/
noncomputable def maximizer
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) : E :=
  Classical.choose <|
    K.isCompact.exists_isMaxOn K.nonempty ℓ.continuous.continuousOn

/-- The selected point belongs to the compact set. -/
theorem maximizer_mem
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    maximizer K ℓ ∈ (K : Set E) :=
  (Classical.choose_spec <|
    K.isCompact.exists_isMaxOn K.nonempty ℓ.continuous.continuousOn).1

/-- Every point of the compact set lies below the selected maximum. -/
theorem le_maximizer
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ)
    {x : E} (hx : x ∈ (K : Set E)) :
    ℓ x ≤ ℓ (maximizer K ℓ) :=
  (Classical.choose_spec <|
    K.isCompact.exists_isMaxOn K.nonempty ℓ.continuous.continuousOn).2 hx

/-- Maximum value of a continuous linear functional on a nonempty compact set. -/
noncomputable def maxValue
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) : ℝ :=
  ℓ (maximizer K ℓ)

/-- The points of a compact set attaining the maximum of `ℓ`. -/
def maxSlice
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) : Set E :=
  {x ∈ (K : Set E) | ℓ x = maxValue K ℓ}

/-- The selected maximizer belongs to the maximum slice. -/
theorem maximizer_mem_maxSlice
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    maximizer K ℓ ∈ maxSlice K ℓ := by
  exact ⟨maximizer_mem K ℓ, rfl⟩

/-- A maximum slice is nonempty. -/
theorem maxSlice_nonempty
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    (maxSlice K ℓ).Nonempty :=
  ⟨maximizer K ℓ, maximizer_mem_maxSlice K ℓ⟩

/-- A maximum slice is compact. -/
theorem maxSlice_isCompact
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    IsCompact (maxSlice K ℓ) := by
  have hclosed : IsClosed {x : E | ℓ x = maxValue K ℓ} :=
    isClosed_eq ℓ.continuous continuous_const
  exact K.isCompact.inter_right hclosed

/-- Bundle the maximum slice as a nonempty compact set. -/
noncomputable def refine
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    TopologicalSpace.NonemptyCompacts E where
  carrier := maxSlice K ℓ
  isCompact' := maxSlice_isCompact K ℓ
  nonempty' := maxSlice_nonempty K ℓ

@[simp] theorem mem_refine
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) {x : E} :
    x ∈ (refine K ℓ : Set E) ↔ x ∈ (K : Set E) ∧ ℓ x = maxValue K ℓ :=
  Iff.rfl

end NonemptyCompacts

open NonemptyCompacts

/-- The support face of the convex hull cut out by the raw maximum value. -/
def supportFace [FiniteDimensional ℝ E]
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) : Set E :=
  {x ∈ convexHull ℝ (K : Set E) | ℓ x = maxValue K ℓ}

/-- The convex hull of the raw maximum slice is exactly the corresponding support face. -/
theorem convexHull_maxSlice_eq_supportFace [FiniteDimensional ℝ E]
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) :
    convexHull ℝ (maxSlice K ℓ) = supportFace K ℓ := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨convexHull_mono (fun y hy => hy.1) hx, ?_⟩
    have hlevelConvex : Convex ℝ {y : E | ℓ y = maxValue K ℓ} := by
      intro y hy z hz a b ha hb hab
      change ℓ (a • y + b • z) = maxValue K ℓ
      change ℓ y = maxValue K ℓ at hy
      change ℓ z = maxValue K ℓ at hz
      simp only [map_add, map_smul, smul_eq_mul, hy, hz]
      rw [← add_mul, hab, one_mul]
    exact convexHull_min (fun y hy => hy.2) hlevelConvex hx
  · rintro ⟨hxHull, hxLevel⟩
    rw [_root_.convexHull_eq] at hxHull ⊢
    rcases hxHull with ⟨ι, t, w, z, hw0, hw1, hz, hcenter⟩
    have hlinear : ℓ x = ∑ i ∈ t, w i * ℓ (z i) := by
      rw [← hcenter, Finset.centerMass_eq_of_sum_1 _ _ hw1]
      simp
    have hgap_nonneg :
        ∀ i ∈ t, 0 ≤ w i * (maxValue K ℓ - ℓ (z i)) := by
      intro i hi
      exact mul_nonneg (hw0 i hi)
        (sub_nonneg.mpr (le_maximizer K ℓ (hz i hi)))
    have hgap_sum :
        ∑ i ∈ t, w i * (maxValue K ℓ - ℓ (z i)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
      rw [← hlinear, hxLevel, sub_self]
    have hgap_zero :
        ∀ i ∈ t, w i * (maxValue K ℓ - ℓ (z i)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hgap_nonneg).1 hgap_sum
    let t' : Finset ι := t.filter fun i => w i ≠ 0
    refine ⟨ι, t', w, z, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hw0 i (Finset.mem_filter.1 hi).1
    · calc
        ∑ i ∈ t', w i = ∑ i ∈ t, w i := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hit'
          by_contra hwi
          apply hit'
          change i ∈ t.filter fun j => w j ≠ 0
          exact Finset.mem_filter.2 ⟨hi, hwi⟩
        _ = 1 := hw1
    · intro i hi
      have hit : i ∈ t := (Finset.mem_filter.1 hi).1
      have hwi : w i ≠ 0 := (Finset.mem_filter.1 hi).2
      have hprod := hgap_zero i hit
      have hgap : maxValue K ℓ - ℓ (z i) = 0 :=
        (mul_eq_zero.mp hprod).resolve_left hwi
      exact ⟨hz i hit, (sub_eq_zero.mp hgap).symm⟩
    · calc
        t'.centerMass w z = t.centerMass w z := by
          simpa [t'] using
            (Finset.centerMass_filter_ne_zero (t := t) (w := w) (z := z))
        _ = x := hcenter

/-- Every point of the convex hull lies below the maximum on its compact generator. -/
theorem le_maxValue_of_mem_convexHull [FiniteDimensional ℝ E]
    (K : TopologicalSpace.NonemptyCompacts E) (ℓ : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ convexHull ℝ (K : Set E)) :
    ℓ x ≤ maxValue K ℓ := by
  have hhalf : Convex ℝ {y : E | ℓ y ≤ maxValue K ℓ} := by
    intro y hy z hz a b ha hb hab
    change ℓ (a • y + b • z) ≤ maxValue K ℓ
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      a * ℓ y + b * ℓ z ≤ a * maxValue K ℓ + b * maxValue K ℓ :=
        add_le_add
          (mul_le_mul_of_nonneg_left hy ha)
          (mul_le_mul_of_nonneg_left hz hb)
      _ = maxValue K ℓ := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (fun y hy => le_maximizer K ℓ hy) hhalf hx

/-- Equal convex hulls give equal maximum values for every continuous linear functional. -/
theorem maxValue_eq_of_convexHull_eq [FiniteDimensional ℝ E]
    (K L : TopologicalSpace.NonemptyCompacts E)
    (hHull : convexHull ℝ (K : Set E) = convexHull ℝ (L : Set E))
    (ℓ : E →L[ℝ] ℝ) :
    maxValue K ℓ = maxValue L ℓ := by
  apply le_antisymm
  · have hx : maximizer K ℓ ∈ convexHull ℝ (L : Set E) := by
      rw [← hHull]
      exact subset_convexHull ℝ _ (maximizer_mem K ℓ)
    simpa [maxValue] using le_maxValue_of_mem_convexHull L ℓ hx
  · have hy : maximizer L ℓ ∈ convexHull ℝ (K : Set E) := by
      rw [hHull]
      exact subset_convexHull ℝ _ (maximizer_mem L ℓ)
    simpa [maxValue] using le_maxValue_of_mem_convexHull K ℓ hy

/-- Cutting two compact generators by the same functional preserves equality of convex hulls. -/
theorem refine_convexHull_eq [FiniteDimensional ℝ E]
    (K L : TopologicalSpace.NonemptyCompacts E)
    (hHull : convexHull ℝ (K : Set E) = convexHull ℝ (L : Set E))
    (ℓ : E →L[ℝ] ℝ) :
    convexHull ℝ (refine K ℓ : Set E) =
      convexHull ℝ (refine L ℓ : Set E) := by
  change convexHull ℝ (maxSlice K ℓ) = convexHull ℝ (maxSlice L ℓ)
  rw [convexHull_maxSlice_eq_supportFace K ℓ,
      convexHull_maxSlice_eq_supportFace L ℓ]
  have hmax := maxValue_eq_of_convexHull_eq K L hHull ℓ
  ext x
  simp [supportFace, hHull, hmax]

/-- Successive maximum refinement by an ordered finite dictionary of functionals. -/
noncomputable def lexicographicRefine :
    List (E →L[ℝ] ℝ) → TopologicalSpace.NonemptyCompacts E →
      TopologicalSpace.NonemptyCompacts E
  | [], K => K
  | ℓ :: ls, K => lexicographicRefine ls (refine K ℓ)

/-- A full lexicographic refinement stays inside its input compact set. -/
theorem lexicographicRefine_subset
    (ls : List (E →L[ℝ] ℝ)) (K : TopologicalSpace.NonemptyCompacts E) :
    (lexicographicRefine ls K : Set E) ⊆ (K : Set E) := by
  induction ls generalizing K with
  | nil =>
      intro x hx
      exact hx
  | cons ℓ ls ih =>
      intro x hx
      have hxTail : x ∈ (lexicographicRefine ls (refine K ℓ) : Set E) := by
        simpa [lexicographicRefine] using hx
      have hxRefine : x ∈ (refine K ℓ : Set E) :=
        ih (K := refine K ℓ) hxTail
      exact ((mem_refine K ℓ).1 hxRefine).1

/-- Survivors of the listed refinements agree under every listed functional. -/
theorem lexicographicRefine_agreesOn
    (ls : List (E →L[ℝ] ℝ)) (K : TopologicalSpace.NonemptyCompacts E)
    {x y : E}
    (hx : x ∈ (lexicographicRefine ls K : Set E))
    (hy : y ∈ (lexicographicRefine ls K : Set E)) :
    ∀ ℓ ∈ ls, ℓ x = ℓ y := by
  induction ls generalizing K x y with
  | nil =>
      intro ℓ hℓ
      simp at hℓ
  | cons ℓ ls ih =>
      intro φ hφ
      have hxTail : x ∈ (lexicographicRefine ls (refine K ℓ) : Set E) := by
        simpa [lexicographicRefine] using hx
      have hyTail : y ∈ (lexicographicRefine ls (refine K ℓ) : Set E) := by
        simpa [lexicographicRefine] using hy
      have hxRefine : x ∈ (refine K ℓ : Set E) :=
        lexicographicRefine_subset ls (refine K ℓ) hxTail
      have hyRefine : y ∈ (refine K ℓ : Set E) :=
        lexicographicRefine_subset ls (refine K ℓ) hyTail
      rcases List.mem_cons.mp hφ with hφℓ | hφTail
      · subst φ
        exact ((mem_refine K ℓ).1 hxRefine).2.trans
          ((mem_refine K ℓ).1 hyRefine).2.symm
      · exact ih (K := refine K ℓ) hxTail hyTail φ hφTail

/-- A point-separating dictionary leaves at most one survivor. -/
theorem lexicographicRefine_subsingleton
    (ls : List (E →L[ℝ] ℝ))
    (hsep : ∀ x y : E, (∀ ℓ ∈ ls, ℓ x = ℓ y) → x = y)
    (K : TopologicalSpace.NonemptyCompacts E) :
    (lexicographicRefine ls K : Set E).Subsingleton := by
  intro x hx y hy
  exact hsep x y (lexicographicRefine_agreesOn ls K hx hy)

/-- Repeated lexicographic refinement preserves equality of convex hulls. -/
theorem lexicographicRefine_convexHull_eq [FiniteDimensional ℝ E]
    (ls : List (E →L[ℝ] ℝ))
    (K L : TopologicalSpace.NonemptyCompacts E)
    (hHull : convexHull ℝ (K : Set E) = convexHull ℝ (L : Set E)) :
    convexHull ℝ (lexicographicRefine ls K : Set E) =
      convexHull ℝ (lexicographicRefine ls L : Set E) := by
  induction ls generalizing K L with
  | nil =>
      simpa [lexicographicRefine] using hHull
  | cons ℓ ls ih =>
      simp only [lexicographicRefine]
      exact ih
        (K := refine K ℓ)
        (L := refine L ℓ)
        (refine_convexHull_eq K L hHull ℓ)

/-- A common raw generator selected by a finite point-separating dictionary.

The conclusion deliberately retains `Good z`; this theorem is not merely an
intersection statement. -/
theorem exists_common_of_convexHull_eq [FiniteDimensional ℝ E]
    (ls : List (E →L[ℝ] ℝ))
    (hsep : ∀ x y : E, (∀ ℓ ∈ ls, ℓ x = ℓ y) → x = y)
    (K L : TopologicalSpace.NonemptyCompacts E)
    (hHull : convexHull ℝ (K : Set E) = convexHull ℝ (L : Set E))
    (ℓ : E →L[ℝ] ℝ)
    (Good : E → Prop)
    (hgood : ∀ z ∈ maxSlice L ℓ, Good z) :
    ∃ z, z ∈ (K : Set E) ∧ z ∈ (L : Set E) ∧ Good z := by
  have hSliceHull :
      convexHull ℝ (refine K ℓ : Set E) =
        convexHull ℝ (refine L ℓ : Set E) :=
    refine_convexHull_eq K L hHull ℓ
  have hFinalHull :
      convexHull ℝ (lexicographicRefine ls (refine K ℓ) : Set E) =
        convexHull ℝ (lexicographicRefine ls (refine L ℓ) : Set E) :=
    lexicographicRefine_convexHull_eq ls (refine K ℓ) (refine L ℓ) hSliceHull
  rcases (lexicographicRefine ls (refine K ℓ)).nonempty with ⟨x, hx⟩
  rcases (lexicographicRefine ls (refine L ℓ)).nonempty with ⟨y, hy⟩
  have hsubL :
      (lexicographicRefine ls (refine L ℓ) : Set E).Subsingleton :=
    lexicographicRefine_subsingleton ls hsep (refine L ℓ)
  have hLsingleton :
      (lexicographicRefine ls (refine L ℓ) : Set E) = {y} :=
    hsubL.eq_singleton_of_mem hy
  have hxHullL :
      x ∈ convexHull ℝ (lexicographicRefine ls (refine L ℓ) : Set E) := by
    rw [← hFinalHull]
    exact subset_convexHull ℝ _ hx
  have hxy : x = y := by
    rw [hLsingleton, convexHull_singleton] at hxHullL
    simpa using hxHullL
  have hxK0 : x ∈ (refine K ℓ : Set E) :=
    lexicographicRefine_subset ls (refine K ℓ) hx
  have hyL0 : y ∈ (refine L ℓ : Set E) :=
    lexicographicRefine_subset ls (refine L ℓ) hy
  have hxL0 : x ∈ (refine L ℓ : Set E) := by
    simpa [hxy] using hyL0
  have hxK : x ∈ (K : Set E) := ((mem_refine K ℓ).1 hxK0).1
  have hxL : x ∈ (L : Set E) := ((mem_refine L ℓ).1 hxL0).1
  have hxSlice : x ∈ maxSlice L ℓ := by
    exact (mem_refine L ℓ).1 hxL0
  exact ⟨x, hxK, hxL, hgood x hxSlice⟩

/-- Coordinate projection on a finite real Pi space. -/
noncomputable def coordinate {ι : Type*} [Fintype ι] (i : ι) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

/-- Every coordinate projection, in a fixed finite enumeration. -/
noncomputable def allCoordinates {ι : Type*} [Fintype ι] :
    List ((ι → ℝ) →L[ℝ] ℝ) := by
  classical
  exact Finset.univ.toList.map (fun i : ι => coordinate i)

@[simp] theorem coordinate_mem_allCoordinates {ι : Type*} [Fintype ι]
    (i : ι) :
    coordinate i ∈ (allCoordinates : List ((ι → ℝ) →L[ℝ] ℝ)) := by
  classical
  simp [allCoordinates]

/-- All coordinate projections separate points of a finite real Pi space. -/
theorem allCoordinates_separate {ι : Type*} [Fintype ι]
    (x y : ι → ℝ)
    (h : ∀ ℓ ∈ (allCoordinates : List ((ι → ℝ) →L[ℝ] ℝ)), ℓ x = ℓ y) :
    x = y := by
  funext i
  have hi := h (coordinate i) (coordinate_mem_allCoordinates i)
  simpa [coordinate] using hi

/-- Finite-coordinate common-generator extraction with the full `Good` conclusion. -/
theorem exists_common_pi {ι : Type*} [Fintype ι]
    (K L : TopologicalSpace.NonemptyCompacts (ι → ℝ))
    (hHull : convexHull ℝ (K : Set (ι → ℝ)) =
      convexHull ℝ (L : Set (ι → ℝ)))
    (ℓ : (ι → ℝ) →L[ℝ] ℝ)
    (Good : (ι → ℝ) → Prop)
    (hgood : ∀ z ∈ maxSlice L ℓ, Good z) :
    ∃ z, z ∈ (K : Set (ι → ℝ)) ∧ z ∈ (L : Set (ι → ℝ)) ∧ Good z := by
  exact exists_common_of_convexHull_eq
    (allCoordinates : List ((ι → ℝ) →L[ℝ] ℝ))
    allCoordinates_separate K L hHull ℓ Good hgood

end MathlibAnnex
