/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRSubalgebra

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.Analysis.CStarAlgebra

universe u v

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

variable {A : Type u} [CStarAlgebra A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]

section ConcreteIdeals

variable (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
variable (hfree : ∀ d : D,
  IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) →
    (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0)

-- The candidate is an actual norm-closed two-sided ideal of the ambient algebra.
example {J : TwoSidedIdeal A} (hJ : J ∈ pureStateCompactPreimageIdeals D phi) :
    IsClosed (J : Set A) ∧ J ≠ ⊤ :=
  ⟨isClosed_of_mem_pureStateCompactPreimageIdeals D phi hJ,
    ne_top_of_mem_pureStateCompactPreimageIdeals D phi hphi.1 hfree hJ⟩

-- Its intersection is killed by the original GNS operator, not only by one coefficient.
example {J : TwoSidedIdeal A} (hJ : J ∈ pureStateCompactPreimageIdeals D phi)
    (d : D) (hd : (d : A) ∈ J) :
    (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 :=
  gns_map_eq_zero_of_mem_pureStateCompactPreimageIdeals D phi hphi.1 hfree hJ d hd

-- The empty chain is covered by an actual pure extension.
example [Nontrivial A] :
    ∃ J ∈ pureStateCompactPreimageIdeals D phi,
      ∀ I ∈ (∅ : Set (TwoSidedIdeal A)), I ≤ J :=
  exists_upper_bound_pureStateCompactPreimageIdeals D phi hphi hfree ∅
    (by simp) (by simp)

-- No assumed chain-upper-bound principle appears in this consumer's hypotheses.
example [Nontrivial A] (C : Set (TwoSidedIdeal A))
    (hC : C ⊆ pureStateCompactPreimageIdeals D phi) (hchain : IsChain (· ≤ ·) C) :
    ∃ J ∈ pureStateCompactPreimageIdeals D phi, ∀ I ∈ C, I ≤ J :=
  exists_upper_bound_pureStateCompactPreimageIdeals D phi hphi hfree C hC hchain

example [Nontrivial A] :
    ∃ J : TwoSidedIdeal A,
      Maximal (· ∈ pureStateCompactPreimageIdeals D phi) J ∧ J ≠ ⊤ :=
  exists_maximal_pureStateCompactPreimageIdeals D phi hphi hfree

end ConcreteIdeals

-- The maximality contradiction constructs a genuine nonzero compact GNS image.
example (hA : IsGCR A) (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi) :
    ∃ d : D, (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d ≠ 0 ∧
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) :=
  hA.exists_nonzero_compact_gnsStarAlgHom D phi hphi

-- Endpoint: arbitrary closed same-unit subalgebras, without Nontrivial or separability.
example (hA : IsGCR A) : IsGCR D := hA.starSubalgebra D

-- The zero ambient algebra is included by the same endpoint.
example [Subsingleton A] : IsGCR D :=
  (isGCR_of_subsingleton (A := A)).starSubalgebra D

-- The final statement supplies literal preimages of all compact operators on
-- an independently specified Hilbert universe.
example (hA : IsGCR A) {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (pi : NonUnitalCStarRepresentation D H) (hpi : pi.IsIrreducible)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) : ∃ d : D, pi d = T :=
  (NonUnitalStarAlgHom.mem_range pi).1
    ((hA.starSubalgebra D).compact_le_range pi hpi hT)
