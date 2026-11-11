/-
New source candidate; intended license: Apache-2.0.
Publication of this exact contribution requires the owner's grant.
Upstream origins and retained terms are recorded in notices/UPSTREAM_THIRD_PARTY_NOTICES.md.

The compact preimage ideal is the existing construction from
MathlibAnnex/Analysis/CStarAlgebra/CompactPreimage.lean. The approximation
argument is based on Sakai, On type I C*-algebras, Proc. Amer. Math. Soc.
18 (1967), 861--863, p. 862. The Lean proofs below are new.
-/

import MathlibAnnex.Analysis.CStarAlgebra.CompactPreimage
import MathlibAnnex.Analysis.CStarAlgebra.Spectrum.Kernel
import MathlibAnnex.Analysis.InnerProductSpace.CompactOperatorAlgebra
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PureStateExtension

/-!
# Compact-preimage chains and compressed approximants

The analytic step in the compact-ideal maximality argument permits different
ambient Hilbert spaces for different approximants. An actual linear isometry
intertwining the subalgebra action supplies each compression. Uniform
contractivity then puts the fixed subalgebra operator in the norm closure of
the compact operators.

The closed upper bound is constructed from the directed union of the
existing compact preimage ideals. The statement that this upper bound is
itself the compact preimage of a pure state is a separate assertion.
-/

noncomputable section

set_option autoImplicit false
noncomputable section

open Set
open MathlibAnnex.CStarAlgebra
open scoped CStarAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

section Compression

variable {H : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compression along an isometry is contractive, including the zero space. -/
theorem norm_isometry_compression_le (U : H →ₗᵢ[ℂ] K) (T : K →L[ℂ] K) :
    ‖U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap)‖ ≤ ‖T‖ := by
  have hU : ‖U.toContinuousLinearMap‖ ≤ 1 := U.norm_toContinuousLinearMap_le
  have hUstar : ‖U.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hU
  calc
    ‖U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap)‖ ≤
        ‖U.toContinuousLinearMap.adjoint‖ * ‖T ∘L U.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖U.toContinuousLinearMap.adjoint‖ * (‖T‖ * ‖U.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by simp

/-- An isometric intertwiner identifies the compressed ambient action with
the original action; surjectivity onto the ambient Hilbert space is unnecessary. -/
theorem isometry_compression_eq_of_intertwines
    (U : H →ₗᵢ[ℂ] K) (S : H →L[ℂ] H) (T : K →L[ℂ] K)
    (hU : ∀ x : H, U (S x) = T (U x)) :
    U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap) = S := by
  have hTU : T ∘L U.toContinuousLinearMap = U.toContinuousLinearMap ∘L S := by
    ext x
    exact (hU x).symm
  rw [hTU, ← ContinuousLinearMap.comp_assoc, U.adjoint_comp_self]
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- Compact operators remain compact under actual isometric compression. -/
theorem isCompactOperator_isometry_compression
    (U : H →ₗᵢ[ℂ] K) {T : K →L[ℂ] K} (hT : IsCompactOperator T) :
    IsCompactOperator
      (U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap)) :=
  (hT.comp_clm U.toContinuousLinearMap).clm_comp U.toContinuousLinearMap.adjoint

end Compression

section CompactPreimage

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A genuine nonzero compact image makes the compact preimage strictly
larger than the representation kernel. -/
theorem NonUnitalCStarRepresentation.kernelIdeal_lt_compactPreimageIdeal
    (pi : NonUnitalCStarRepresentation A H)
    (hnz : ∃ a : A, IsCompactOperator (pi a) ∧ pi a ≠ 0) :
    pi.kernelIdeal < compactPreimageIdeal pi := by
  apply lt_iff_le_not_ge.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    apply (mem_compactPreimageIdeal pi a).2
    rw [(pi.mem_kernelIdeal a).1 ha]
    exact isCompactOperator_zero
  · intro hle
    obtain ⟨a, haK, ha0⟩ := hnz
    exact ha0 ((pi.mem_kernelIdeal a).1 (hle ((mem_compactPreimageIdeal pi a).2 haK)))

end CompactPreimage

section Family

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type w} {K : ι → Type z}
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℂ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The compact-approximation step for a family of representations on
possibly different Hilbert spaces. The membership hypothesis concerns the
ambient norm closure; the approximating elements need not lie in `D`. -/
theorem isCompactOperator_of_mem_closure_iUnion_compactPreimageIdeal
    (D : NonUnitalStarSubalgebra ℂ A) [NonUnitalCStarAlgebra D]
    (pi : NonUnitalCStarRepresentation D H)
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (U : ∀ i, H →ₗᵢ[ℂ] K i)
    (hU : ∀ (i : ι) (d : D) (x : H), U i (pi d x) = rho i (d : A) (U i x))
    (b : D)
    (hb : (b : A) ∈ closure (⋃ i, (compactPreimageIdeal (rho i) : Set A))) :
    IsCompactOperator (pi b) := by
  have hclosure : pi b ∈ closure {T : H →L[ℂ] H | IsCompactOperator T} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨a, ha, hab⟩ := (Metric.mem_closure_iff.mp hb) ε hε
    obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
    let u : H →L[ℂ] K i := (U i).toContinuousLinearMap
    let T : H →L[ℂ] H := u.adjoint ∘L (rho i a ∘L u)
    have hT : IsCompactOperator T :=
      isCompactOperator_isometry_compression (U i) ((mem_compactPreimageIdeal (rho i) a).1 hai)
    have hcomp : u.adjoint ∘L (rho i (b : A) ∘L u) = pi b :=
      isometry_compression_eq_of_intertwines (U i) (pi b) (rho i (b : A)) (hU i b)
    have hdiff : pi b - T = u.adjoint ∘L (rho i ((b : A) - a) ∘L u) := by
      ext x
      have hx := congrArg (fun S : H →L[ℂ] H => S x) hcomp
      change u.adjoint (rho i (b : A) (u x)) = pi b x at hx
      change pi b x - u.adjoint (rho i a (u x)) =
        u.adjoint (rho i ((b : A) - a) (u x))
      rw [map_sub, ContinuousLinearMap.sub_apply, map_sub, hx]
    have hdist : dist (pi b) T ≤ dist (b : A) a := by
      rw [dist_eq_norm, dist_eq_norm, hdiff]
      exact (norm_isometry_compression_le (U i) (rho i ((b : A) - a))).trans
        (NonUnitalStarAlgHom.norm_apply_le (rho i) ((b : A) - a))
    exact ⟨T, hT, lt_of_le_of_lt hdist hab⟩
  simpa only [isClosed_setOfPred_isCompactOperator.closure_eq, Set.mem_setOf_eq] using hclosure

/-- The preceding norm approximation gives the precise kernel containment
used for a compact-free subalgebra representation. -/
theorem map_eq_zero_of_mem_closure_iUnion_compactPreimageIdeal
    (D : NonUnitalStarSubalgebra ℂ A) [NonUnitalCStarAlgebra D]
    (pi : NonUnitalCStarRepresentation D H)
    (hfree : ∀ d : D, IsCompactOperator (pi d) → pi d = 0)
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (U : ∀ i, H →ₗᵢ[ℂ] K i)
    (hU : ∀ (i : ι) (d : D) (x : H), U i (pi d x) = rho i (d : A) (U i x))
    (b : D)
    (hb : (b : A) ∈ closure (⋃ i, (compactPreimageIdeal (rho i) : Set A))) :
    pi b = 0 :=
  hfree b (isCompactOperator_of_mem_closure_iUnion_compactPreimageIdeal D pi rho U hU b hb)

variable [Nonempty ι]

/-- The existing directed-supremum theorem identifies the star-subalgebra
supremum with the union of the existing ideal carriers. -/
private theorem coe_iSup_compact_preimage
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i))) :
    ((⨆ i, NonUnitalStarSubalgebra.comap (rho i)
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K i)) :
          NonUnitalStarSubalgebra ℂ A) : Set A) =
      ⋃ i, (compactPreimageIdeal (rho i) : Set A) := by
  have hdir' : Directed (· ≤ ·) (fun i =>
      NonUnitalStarSubalgebra.comap (rho i)
        (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K i))) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_, ?_⟩
    · intro a ha
      exact (mem_compactPreimageIdeal (rho k) a).1
        (hik ((mem_compactPreimageIdeal (rho i) a).2 ha))
    · intro a ha
      exact (mem_compactPreimageIdeal (rho k) a).1
        (hjk ((mem_compactPreimageIdeal (rho j) a).2 ha))
  rw [NonUnitalStarSubalgebra.coe_iSup_of_directed hdir']
  ext a
  simp only [Set.mem_iUnion, SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap,
    ContinuousLinearMap.mem_compactOperatorStarSubalgebra, mem_compactPreimageIdeal]

/-- The norm closure of a directed union of compact preimage ideals,
bundled using the existing algebraic two-sided ideal type. -/
def compactPreimageDirectedSup
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i))) : TwoSidedIdeal A := by
  let S : NonUnitalStarSubalgebra ℂ A :=
    ⨆ i, NonUnitalStarSubalgebra.comap (rho i)
      (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K i))
  have hS : (S : Set A) = ⋃ i, (compactPreimageIdeal (rho i) : Set A) :=
    coe_iSup_compact_preimage rho hdir
  refine TwoSidedIdeal.mk' (S.topologicalClosure : Set A)
    S.topologicalClosure.zero_mem
    (fun {a b} ha hb => S.topologicalClosure.add_mem ha hb)
    (fun {a} ha => S.topologicalClosure.neg_mem ha) ?_ ?_
  · intro a b hb
    change a * b ∈ closure (S : Set A)
    exact map_mem_closure (continuous_const.mul continuous_id) hb (fun x hx => by
      rw [hS] at hx ⊢
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, (compactPreimageIdeal (rho i)).mul_mem_left a x hxi⟩)
  · intro a b ha
    change a * b ∈ closure (S : Set A)
    exact map_mem_closure (f := fun x : A => x * b) (continuous_id.mul continuous_const) ha (fun x hx => by
      rw [hS] at hx ⊢
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, (compactPreimageIdeal (rho i)).mul_mem_right x b hxi⟩)

/-- The new ideal is literally the norm closure of the union of the
pre-existing compact preimages. -/
theorem coe_compactPreimageDirectedSup
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i))) :
    (compactPreimageDirectedSup rho hdir : Set A) =
      closure (⋃ i, (compactPreimageIdeal (rho i) : Set A)) := by
  simp only [compactPreimageDirectedSup, TwoSidedIdeal.coe_mk']
  change closure (((⨆ i, NonUnitalStarSubalgebra.comap (rho i)
    (ContinuousLinearMap.compactOperatorStarSubalgebra ℂ (K i))) :
      NonUnitalStarSubalgebra ℂ A) : Set A) = _
  rw [coe_iSup_compact_preimage rho hdir]

/-- The directed upper bound is closed in the original algebra norm. -/
theorem isClosed_compactPreimageDirectedSup
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i))) :
    IsClosed (compactPreimageDirectedSup rho hdir : Set A) := by
  rw [coe_compactPreimageDirectedSup]
  exact isClosed_closure

/-- Each compact preimage is contained in the constructed closed upper bound. -/
theorem compactPreimageIdeal_le_directed_sup
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i))) (i : ι) :
    compactPreimageIdeal (rho i) ≤ compactPreimageDirectedSup rho hdir := by
  intro a ha
  have ha' : a ∈ closure (⋃ j, (compactPreimageIdeal (rho j) : Set A)) :=
    subset_closure (Set.mem_iUnion.mpr ⟨i, ha⟩)
  rwa [← coe_compactPreimageDirectedSup rho hdir] at ha'

/-- Least-upper-bound property among norm-closed two-sided ideals. -/
theorem compactPreimageDirectedSup_le
    (rho : ∀ i, NonUnitalCStarRepresentation A (K i))
    (hdir : Directed (· ≤ ·) (fun i => compactPreimageIdeal (rho i)))
    (J : TwoSidedIdeal A) (hJ : IsClosed (J : Set A))
    (hbound : ∀ i, compactPreimageIdeal (rho i) ≤ J) :
    compactPreimageDirectedSup rho hdir ≤ J := by
  intro a ha
  have ha' : a ∈ closure (⋃ i, (compactPreimageIdeal (rho i) : Set A)) := by
    rwa [← coe_compactPreimageDirectedSup rho hdir]
  apply closure_minimal (s := ⋃ i, (compactPreimageIdeal (rho i) : Set A)) ?_ hJ ha'
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact hbound i hxi

end Family

section StateExtensions

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
variable [PartialOrder D] [StarOrderedRing D]
variable {ι : Type w}

/-- For actual extensions of a fixed state, the needed cyclic isometries
are constructed from their GNS models. Thus the compact-approximation
conclusion has no supplied compression or intertwiner hypothesis. -/
theorem isCompactOperator_gns_of_mem_closure_iUnion_compactPreimageIdeal
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D)
    (psi : ι → A →L[ℂ] ℂ) (hpsi : ∀ i, psi i ∈ stateSpace A)
    (hext : ∀ (i : ι) (d : D), psi i d = phi d)
    (b : D)
    (hb : (b : A) ∈ closure (⋃ i, (compactPreimageIdeal
      (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).gnsStarAlgHom.toNonUnitalStarAlgHom :
        Set A))) :
    IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom b) := by
  classical
  choose U hU using fun i =>
    exists_gns_isometry_of_state_extension D phi hphi (psi i) (hpsi i) (hext i)
  letI : NonUnitalCStarAlgebra D.toNonUnitalStarSubalgebra :=
    inferInstanceAs (NonUnitalCStarAlgebra D)
  exact isCompactOperator_of_mem_closure_iUnion_compactPreimageIdeal
    D.toNonUnitalStarSubalgebra
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.toNonUnitalStarAlgHom
    (fun i =>
      (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).gnsStarAlgHom.toNonUnitalStarAlgHom)
    U (fun i => (hU i).2) b hb

/-- The intersection of the norm-closed union with the original subalgebra
lies in the fixed GNS kernel whenever that GNS image has no nonzero compact
operator. The extension states are concrete, not hypothetical intertwiners. -/
theorem gns_map_eq_zero_of_mem_closure_iUnion_compactPreimageIdeal
    (phi : D →L[ℂ] ℂ) (hphi : phi ∈ stateSpace D)
    (hfree : ∀ d : D,
      IsCompactOperator ((positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d) →
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom d = 0)
    (psi : ι → A →L[ℂ] ℂ) (hpsi : ∀ i, psi i ∈ stateSpace A)
    (hext : ∀ (i : ι) (d : D), psi i d = phi d)
    (b : D)
    (hb : (b : A) ∈ closure (⋃ i, (compactPreimageIdeal
      (positiveLinearMapOfMemStateSpace (psi i) (hpsi i)).gnsStarAlgHom.toNonUnitalStarAlgHom :
        Set A))) :
    (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom b = 0 :=
  hfree b (isCompactOperator_gns_of_mem_closure_iUnion_compactPreimageIdeal
    D phi hphi psi hpsi hext b hb)

end StateExtensions

end MathlibAnnex.Analysis.CStarAlgebra
