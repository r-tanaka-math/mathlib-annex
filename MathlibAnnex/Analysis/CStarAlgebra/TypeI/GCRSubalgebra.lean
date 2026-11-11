/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Order.Zorn
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.CompactIdealMaximality
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.GCRPermanence
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.QuotientPureState
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.IrreduciblePure
import MathlibAnnex.Analysis.CStarAlgebra.PureStateGNS.VectorState

/-!
# GCR permanence for closed subalgebras with the same unit

The Zorn candidates are actual compact-preimage ideals of pure state
extensions. A chain is bounded by first closing its directed union and then
extending the prescribed state through that genuine quotient. The resulting
state supplies a new candidate ideal containing the whole chain.

For a compact-free prescribed GNS action every candidate is proper. Extending
through a maximal candidate gives an irreducible representation which kills
that ideal. GCR supplies a nonzero compact image, so its compact-preimage ideal
strictly enlarges the candidate. This contradiction yields a nonzero compact
in every prescribed pure GNS action of the subalgebra.

Existing pointed GNS transport and compact-intersection absorption give the
stated GCR predicate, including zero algebras and arbitrary Hilbert universes.
The original algebra and its closed subalgebra share the same unit here.
-/

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.CStarAlgebra
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u

variable {A : Type u} [CStarAlgebra A]

attribute [local instance] _root_.CStarAlgebra.spectralOrder
  _root_.CStarAlgebra.spectralOrderedRing

section Candidates

variable (D : StarSubalgebra ℂ A)

/-- Actual compact-preimage ideals of pure ambient states extending a fixed
functional on the same-unit subalgebra. No order on states is introduced. -/
def pureStateCompactPreimageIdeals (phi : D →L[ℂ] ℂ) : Set (TwoSidedIdeal A) :=
  {J | ∃ (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A),
    IsPureState A psi ∧ (∀ d : D, psi d = phi d) ∧
      J = compactPreimageIdeal
        (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom.toNonUnitalStarAlgHom}

/-- Every member of the candidate family is norm closed in the ambient
algebra, by the existing compact-preimage construction. -/
theorem isClosed_of_mem_pureStateCompactPreimageIdeals
    (phi : D →L[ℂ] ℂ) {J : TwoSidedIdeal A}
    (hJ : J ∈ pureStateCompactPreimageIdeals D phi) : IsClosed (J : Set A) := by
  rcases hJ with ⟨psi, hpsi, _hpure, _hext, rfl⟩
  exact isClosed_compactPreimageIdeal
    (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom.toNonUnitalStarAlgHom

variable [IsClosed (D : Set A)]

/-- The empty chain has an upper bound because the prescribed pure state
has an actual pure ambient extension. -/
theorem pureStateCompactPreimageIdeals_nonempty [Nontrivial A]
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi) :
    (pureStateCompactPreimageIdeals D phi).Nonempty := by
  obtain ⟨psi, hpsi, hpure, hext⟩ := exists_pure_state_extension D phi hphi
  exact ⟨compactPreimageIdeal
      (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom.toNonUnitalStarAlgHom,
    psi, hpsi, hpure, hext, rfl⟩

/-- A candidate ideal meets the subalgebra inside the prescribed GNS kernel
when that action has no nonzero compact operator. -/
theorem gns_map_eq_zero_of_mem_pureStateCompactPreimageIdeals
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0)
    {J : TwoSidedIdeal A} (hJ : J ∈ pureStateCompactPreimageIdeals D phi)
    (d : D) (hd : (d : A) ∈ J) :
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0 := by
  rcases hJ with ⟨psi, hpsi, _hpure, hext, rfl⟩
  obtain ⟨U, _hvector, hU⟩ :=
    exists_gns_isometry_of_state_extension D phi hphi psi hpsi hext
  have hcompression := isometry_compression_eq_of_intertwines U
    ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d)
    ((positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom (d : A)) (hU d)
  apply hfree d
  rw [← hcompression]
  exact isCompactOperator_isometry_compression U
    ((mem_compactPreimageIdeal
      (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom.toNonUnitalStarAlgHom
      (d : A)).1 hd)

/-- The prescribed state excludes the whole ideal: if its GNS action kills
the intersection, membership of the common unit would give `phi 1 = 0`. -/
theorem ne_top_of_gns_eq_zero_on_intersection
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D) (J : TwoSidedIdeal A)
    (hker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0) : J ≠ ⊤ := by
  intro htop
  have hz := hker (1 : D) (by rw [htop]; trivial)
  have hvalue : phi (1 : D) = 0 := by
    rw [← inner_gnsStarAlgHom_stateGNSVector phi hphi (1 : D), hz,
      ContinuousLinearMap.zero_apply, inner_zero_right]
  exact one_ne_zero (hphi.2.symm.trans hvalue)

/-- In particular every compact-preimage candidate is proper. The assertion
uses the original nonzero state and the proved GNS compression. -/
theorem ne_top_of_mem_pureStateCompactPreimageIdeals
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0)
    {J : TwoSidedIdeal A} (hJ : J ∈ pureStateCompactPreimageIdeals D phi) : J ≠ ⊤ :=
  ne_top_of_gns_eq_zero_on_intersection D phi hphi J
    (gns_map_eq_zero_of_mem_pureStateCompactPreimageIdeals D phi hphi hfree hJ)

/-- Every chain of actual compact-preimage candidates has an upper bound in
the same family. Closing the union is only the intermediate ideal; the new
candidate is constructed by pure extension through its actual quotient. -/
theorem exists_upper_bound_pureStateCompactPreimageIdeals [Nontrivial A]
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0)
    (C : Set (TwoSidedIdeal A)) (hC : C ⊆ pureStateCompactPreimageIdeals D phi)
    (hchain : IsChain (· ≤ ·) C) :
    ∃ J ∈ pureStateCompactPreimageIdeals D phi, ∀ I ∈ C, I ≤ J := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hCnonempty
  · obtain ⟨J, hJ⟩ := pureStateCompactPreimageIdeals_nonempty D phi hphi
    exact ⟨J, hJ, by simp⟩
  · letI : Nonempty C := ⟨⟨hCnonempty.choose, hCnonempty.choose_spec⟩⟩
    have hdata : ∀ i : C,
        ∃ (psi : A →L[ℂ] ℂ) (hpsi : psi ∈ stateSpace A),
          IsPureState A psi ∧ (∀ d : D, psi d = phi d) ∧
            i.val = compactPreimageIdeal
              (positiveLinearMapOfMemStateSpace psi hpsi).gnsStarAlgHom.toNonUnitalStarAlgHom :=
      fun i => hC i.property
    choose psi hpsi hpure hext heq using hdata
    let rho (i : C) : NonUnitalCStarRepresentation A
        (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).GNS :=
      (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).gnsStarAlgHom.toNonUnitalStarAlgHom
    have hdir : Directed (· ≤ ·) (fun i : C => compactPreimageIdeal (rho i)) := by
      intro i j
      rcases hchain.total i.property j.property with hij | hji
      · refine ⟨j, ?_, le_rfl⟩
        simpa only [heq i, heq j] using hij
      · refine ⟨i, le_rfl, ?_⟩
        simpa only [heq j, heq i] using hji
    let J : TwoSidedIdeal A := compactPreimageDirectedSup rho hdir
    have hJclosed : IsClosed (J : Set A) := isClosed_compactPreimageDirectedSup rho hdir
    have hJker : ∀ d : D, (d : A) ∈ J →
        (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 := by
      intro d hd
      apply gns_map_eq_zero_of_mem_closure_iUnion_compactPreimageIdeal
        D phi hphi.1 hfree psi hpsi hext d
      change (d : A) ∈ closure (⋃ i : C, (compactPreimageIdeal (rho i) : Set A))
      rw [← coe_compactPreimageDirectedSup rho hdir]
      exact hd
    obtain ⟨omega, homega, homegaPure, homegaExt, homegaZero⟩ :=
      exists_pure_state_extension_annihilating_ideal D phi hphi J hJclosed hJker
    let tau : NonUnitalCStarRepresentation A
        (positiveLinearMapOfMemStateSpace omega homega).GNS :=
      (positiveLinearMapOfMemStateSpace omega homega).gnsStarAlgHom.toNonUnitalStarAlgHom
    have hJtau : J ≤ compactPreimageIdeal tau := by
      intro a ha
      apply (mem_compactPreimageIdeal tau a).2
      have hz : tau a = 0 := homegaZero a ha
      rw [hz]
      exact isCompactOperator_zero
    refine ⟨compactPreimageIdeal tau, ?_, ?_⟩
    · exact ⟨omega, homega, homegaPure, homegaExt, rfl⟩
    · intro I hI
      have hIeq : I = compactPreimageIdeal (rho (⟨I, hI⟩ : C)) := heq ⟨I, hI⟩
      rw [hIeq]
      exact (compactPreimageIdeal_le_directed_sup rho hdir (⟨I, hI⟩ : C)).trans hJtau

/-- Zorn's lemma now applies to the concrete ideal family, and the resulting
maximal ideal is proper by the prescribed nonzero compact-free GNS action. -/
theorem exists_maximal_pureStateCompactPreimageIdeals [Nontrivial A]
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0) :
    ∃ J : TwoSidedIdeal A,
      Maximal (· ∈ pureStateCompactPreimageIdeals D phi) J ∧ J ≠ ⊤ := by
  obtain ⟨J, hJ⟩ := zorn_le₀ (pureStateCompactPreimageIdeals D phi)
    (exists_upper_bound_pureStateCompactPreimageIdeals D phi hphi hfree)
  exact ⟨J, hJ, ne_top_of_mem_pureStateCompactPreimageIdeals D phi hphi.1 hfree hJ.1⟩

end Candidates

/-- Every ordinary pure GNS action of a closed same-unit subalgebra of a GCR
algebra has a nonzero compact image. Extending through a maximal candidate
strictly enlarges its compact-preimage ideal and excludes a compact-free action. -/
theorem IsGCR.exists_nonzero_compact_gnsStarAlgHom (hA : IsGCR A)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (phi : D →L[ℂ] ℂ) (hphi : IsPureState D phi) :
    ∃ d : D, (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d ≠ 0 ∧
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) := by
  classical
  have hone : (1 : A) ≠ 0 := by
    intro hz
    have hzD : (1 : D) = 0 := Subtype.ext hz
    have hvalue : phi (1 : D) = 0 := by rw [hzD, map_zero]
    exact one_ne_zero (hphi.1.2.symm.trans hvalue)
  letI : Nontrivial A := nontrivial_of_ne (1 : A) 0 hone
  by_contra hnone
  have hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 := by
    intro d hd
    by_contra hnonzero
    exact hnone ⟨d, hnonzero, hd⟩
  obtain ⟨J, hJmax, _hJproper⟩ :=
    exists_maximal_pureStateCompactPreimageIdeals D phi hphi hfree
  have hJclosed : IsClosed (J : Set A) :=
    isClosed_of_mem_pureStateCompactPreimageIdeals D phi hJmax.1
  have hJker : ∀ d : D, (d : A) ∈ J →
      (positiveLinearMapOfMemStateSpace phi hphi.1).gnsStarAlgHom d = 0 :=
    gns_map_eq_zero_of_mem_pureStateCompactPreimageIdeals D phi hphi.1 hfree hJmax.1
  obtain ⟨psi, hpsi, hpure, hext, hzero⟩ :=
    exists_pure_state_extension_annihilating_ideal D phi hphi J hJclosed hJker
  let f := positiveLinearMapOfMemStateSpace psi hpsi
  let rho : NonUnitalCStarRepresentation A f.GNS := f.gnsStarAlgHom.toNonUnitalStarAlgHom
  have hnorm : ‖f.gnsCyclicVector‖ = 1 :=
    PositiveLinearMap.norm_gnsCyclicVector f (positiveLinearMapOfMemStateSpace_one psi hpsi)
  have hvector : f.gnsCyclicVector ≠ 0 := by
    intro hz
    simpa [hz] using hnorm
  letI : Nontrivial f.GNS := nontrivial_of_ne f.gnsCyclicVector 0 hvector
  have hrhoU : Representation.IsIrreducible f.gnsStarAlgHom :=
    (Representation.isIrreducible_iff_starAlgHom f.gnsStarAlgHom).2
      (isIrreducible_pureState_gnsStarAlgHom psi hpsi hpure)
  have hrho : rho.IsIrreducible := ⟨hrhoU.1, hrhoU.2⟩
  have hJkernel : J ≤ rho.kernelIdeal := by
    intro a ha
    exact (rho.mem_kernelIdeal a).2 (hzero a ha)
  obtain ⟨a, ha, hcompact⟩ := hA.exists_nonzero_compact_image rho hrho
  have hstrict : J < compactPreimageIdeal rho :=
    lt_of_le_of_lt hJkernel (rho.kernelIdeal_lt_compactPreimageIdeal ⟨a, hcompact, ha⟩)
  have hnew : compactPreimageIdeal rho ∈ pureStateCompactPreimageIdeals D phi :=
    ⟨psi, hpsi, hpure, hext, rfl⟩
  exact (not_le_of_gt hstrict) (hJmax.2 hnew hstrict.le)

private theorem isGCR_of_pureState_ranges {B : Type*} [NonUnitalCStarAlgebra B]
    [ord : PartialOrder B] [hs : StarOrderedRing B]
    (h : ∀ phi : NonUnitalPureState B,
      ContinuousLinearMap.compactOperatorStarSubalgebra ℂ phi.GNS ≤
        NonUnitalStarAlgHom.range phi.gnsRepresentation) : IsGCR B := by
  have heq : ord = _root_.CStarAlgebra.spectralOrder B := by
    apply PartialOrder.ext
    intro x y
    exact (@StarOrderedRing.le_iff B _ ord _ hs x y).trans
      (@StarOrderedRing.le_iff B _ (_root_.CStarAlgebra.spectralOrder B) _
        (_root_.CStarAlgebra.spectralOrderedRing B) x y).symm
  subst ord
  exact h

set_option maxHeartbeats 1500000 in
/-- A closed complex star subalgebra with the same unit as its GCR ambient
algebra is GCR. No nontriviality or separability assumption is added. -/
theorem IsGCR.starSubalgebra (hA : IsGCR A)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)] : IsGCR D := by
  apply isGCR_of_pureState_ranges
  intro phi
  let pi : Representation D phi.GNS :=
    NonUnitalRepresentation.toUnital phi.gnsRepresentation phi.isIrreducible_gnsRepresentation
  have hpi : Representation.IsIrreducible pi :=
    NonUnitalRepresentation.isIrreducible_toUnital phi.gnsRepresentation
      phi.isIrreducible_gnsRepresentation
  obtain ⟨xi, hxi, _hcyclic, _hstate, hU⟩ := irreducible_exists_vectorStateGNS pi hpi
  let psi : D →L[ℂ] ℂ := Representation.vectorFunctional pi xi
  have hpure : IsPureState D psi :=
    isPureState_vectorFunctional_of_isIrreducible pi hpi xi hxi
  let rho : NonUnitalCStarRepresentation D
      (positiveLinearMapOfMemStateSpace psi hpure.1).GNS :=
    (positiveLinearMapOfMemStateSpace psi hpure.1).gnsStarAlgHom.toNonUnitalStarAlgHom
  have hU' : phi.gnsRepresentation.UnitaryEquivalent rho := hU
  obtain ⟨d, hd, hcompact⟩ := hA.exists_nonzero_compact_gnsStarAlgHom D psi hpure
  have hnonzero : phi.gnsRepresentation d ≠ 0 := by
    intro hz
    have hmem : d ∈ rho.kernelIdeal := by
      rw [← hU'.kernelIdeal_eq]
      exact (phi.gnsRepresentation.mem_kernelIdeal d).2 hz
    exact hd ((rho.mem_kernelIdeal d).1 hmem)
  have hcompact' : IsCompactOperator (phi.gnsRepresentation d) :=
    (hU'.isCompactOperator_iff d).2 hcompact
  exact compactOperatorStarSubalgebra_le_of_exists_nonzero_compact
    (NonUnitalStarAlgHom.range phi.gnsRepresentation)
    (HomKernelQuotient.isClosed_image phi.gnsRepresentation)
    ((NonUnitalCStarRepresentation.isIrreducible_imageRepresentation_iff
      phi.gnsRepresentation).2 phi.isIrreducible_gnsRepresentation)
    ⟨phi.gnsRepresentation d,
      (NonUnitalStarAlgHom.mem_range phi.gnsRepresentation).2 ⟨d, rfl⟩,
      hcompact', hnonzero⟩

end MathlibAnnex.Analysis.CStarAlgebra
