/-
Copyright (c) 2026 Ryotaro Tanaka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryotaro Tanaka
-/

import MathlibAnnex.Analysis.CStarAlgebra.DirectSum.ModelEquiv

/-!
# Empty compact-operator c₀-sum models

Two empty index families have the canonical index equivalence, and the general
compact c₀-model assembly therefore gives an actual C-star equivalence.  This
algebraic case is kept separate from the nonempty spectral classification.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped CStarAlgebra

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

variable [IsEmpty ι] [IsEmpty κ]
variable (EA : A ≃⋆ₐ[ℂ] CompactOperatorC0Sum H)
variable (EB : B ≃⋆ₐ[ℂ] CompactOperatorC0Sum K)

/-- The explicit equivalence of two empty index types. -/
def emptyCompactDirectSumIndexEquiv : ι ≃ κ where
  toFun i := isEmptyElim i
  invFun j := isEmptyElim j
  left_inv i := isEmptyElim i
  right_inv j := isEmptyElim j

set_option backward.isDefEq.respectTransparency false in
/-- Empty dependent compact sums are algebraically equivalent without
inventing a spectrum point. -/
def emptyCompactDirectSumModelStarAlgEquiv : A ≃⋆ₐ[ℂ] B :=
  compactDirectSumModelStarAlgEquiv H K EA EB
    (emptyCompactDirectSumIndexEquiv (ι := ι) (κ := κ))
    (fun i => isEmptyElim i)

include EA EB in
set_option backward.isDefEq.respectTransparency false in
/-- The empty/empty endpoint is kept separate from the nonempty spectral
classification. -/
theorem nonempty_starAlgEquiv_of_empty_compact_direct_sum_models :
    Nonempty (A ≃⋆ₐ[ℂ] B) :=
  ⟨emptyCompactDirectSumModelStarAlgEquiv H K EA EB⟩


end MathlibAnnex.Analysis.CStarAlgebra
