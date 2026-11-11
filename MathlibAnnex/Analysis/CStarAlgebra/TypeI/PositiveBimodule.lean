import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import MathlibAnnex.Analysis.CStarAlgebra.PositiveMapBound
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.NormalExtension
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveExtension

/-!
# Compact convex families of positive bimodule extensions

Maps are represented in the product space `A → (H →WOT[ℂ] H)`.
Linearity, positivity, the unit equation, range membership and bimodule
identities are closed conditions in that topology. The existing elementary
bound for a positive unital map places this entire family in a product of
WOT-compact operator balls.

No normality is imposed on a positive map in this family. The source is
unital for these intermediate extension lemmas; its cardinality and the
Hilbert space dimension are unrestricted, and the zero target is retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

open Set Filter Topology
open MathlibAnnex.RepresentedBidual
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every original operator-norm ball is compact in WOT. This is a
specialization of the existing compact bidual image for the identity
representation, using the genuine canonical bidual inclusion. -/
theorem isCompact_wot_norm_le (r : ℝ) :
    IsCompact {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ r} := by
  let rho : (H →L[ℂ] H) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
    NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)
  have himage :
      (fun F : StrongDual ℂ (StrongDual ℂ (H →L[ℂ] H)) =>
        ContinuousLinearMapWOT.ofCLM (extension rho F)) '' Metric.closedBall 0 r =
      {T : H →WOT[ℂ] H | ‖T.toCLM‖ ≤ r} := by
    ext T
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact (norm_extension_apply_le rho F).trans
        ((mem_closedBall_zero_iff (a := F)).mp hF)
    · intro hT
      refine ⟨NormedSpace.inclusionInDoubleDual ℂ (H →L[ℂ] H) T.toCLM, ?_, ?_⟩
      · apply (mem_closedBall_zero_iff (a := NormedSpace.inclusionInDoubleDual ℂ (H →L[ℂ] H) T.toCLM)).mpr
        exact (NormedSpace.double_dual_bound ℂ (H →L[ℂ] H) T.toCLM).trans hT
      · exact congrArg ContinuousLinearMapWOT.ofCLM (extension_canonical rho T.toCLM)
  rw [← himage]
  exact isCompact_wot_extension_closedBall rho r

/-- The positive operator cone is WOT-closed, using the actual Loewner
order and continuous matrix coefficients. -/
theorem isClosed_wot_nonneg :
    IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := by
  have heq : {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} =
      {T : H →WOT[ℂ] H | star T = T} ∩
        ⋂ x : H, {T : H →WOT[ℂ] H | 0 ≤ (inner ℂ x (T x)).re} := by
    ext T
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp h
      exact ⟨ContinuousLinearMapWOT.toCLM_injective hp.isSelfAdjoint,
        fun x => hp.re_inner_nonneg_right x⟩
    · rintro ⟨hs, hp⟩
      apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
      apply ContinuousLinearMap.isPositive_def'.mpr
      refine ⟨congrArg ContinuousLinearMapWOT.toCLM hs, ?_⟩
      intro x
      change 0 ≤ (inner ℂ (T x) x).re
      have hsym : (inner ℂ (T x) x).re = (inner ℂ x (T x)).re := inner_re_symm (𝕜 := ℂ) _ _
      rw [hsym]
      exact hp x
  rw [heq]
  exact (isClosed_eq continuous_star continuous_id).inter
    (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop))

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- All positive unital complex-linear maps, in the topology of pointwise
weak operator convergence. Boundedness follows from positivity; it is not
a further condition in this definition. -/
def positiveUnitalMapSet : Set (A → (H →WOT[ℂ] H)) :=
  {f | (∀ a b : A, f (a + b) = f a + f b) ∧
    (∀ (c : ℂ) (a : A), f (c • a) = c • f a) ∧
    f 1 = 1 ∧ ∀ a : A, 0 ≤ a → 0 ≤ (f a).toCLM}

/-- Recover the actual positive continuous linear map from a member of the
pointwise-WOT family. Continuity is supplied by the existing C-star
positivity theorem. -/
def positiveUnitalMapOfMem (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) :
    A →P[ℂ] (H →L[ℂ] H) :=
  PositiveContinuousLinearMap.ofClass
    (PositiveLinearMap.mk₀
      { toFun := fun a => (f a).toCLM
        map_add' := fun a b => congrArg ContinuousLinearMapWOT.toCLM (hf.1 a b)
        map_smul' := fun c a => congrArg ContinuousLinearMapWOT.toCLM (hf.2.1 c a) }
      (fun a ha => hf.2.2.2 a ha))

@[simp]
theorem positiveUnitalMapOfMem_apply (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) (a : A) :
    positiveUnitalMapOfMem f hf a = (f a).toCLM := rfl

@[simp]
theorem positiveUnitalMapOfMem_one (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) :
    positiveUnitalMapOfMem f hf 1 = 1 :=
  congrArg ContinuousLinearMapWOT.toCLM hf.2.2.1

/-- A genuine positive unital map gives a member of the raw topological
family; no independent boundedness or normality premise is needed. -/
theorem mem_positiveUnitalMapSet (P : A →P[ℂ] (H →L[ℂ] H)) (hP : P 1 = 1) :
    (fun a => ContinuousLinearMapWOT.ofCLM (P a)) ∈
      positiveUnitalMapSet (A := A) (H := H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact congrArg ContinuousLinearMapWOT.ofCLM (map_add P a b)
  · intro c a
    exact congrArg ContinuousLinearMapWOT.ofCLM (map_smul P c a)
  · exact congrArg ContinuousLinearMapWOT.ofCLM hP
  · intro a ha
    exact map_nonneg P ha

/-- The existing four-positive-parts bound is uniform over the entire
family. Its nontrivial-codomain premise is discharged by a separate zero
target branch. -/
theorem norm_le_four_of_mem_positiveUnitalMapSet
    {f : A → (H →WOT[ℂ] H)}
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) (a : A) :
    ‖(f a).toCLM‖ ≤ 4 * ‖a‖ := by
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with h | h
  · letI := h
    rw [Subsingleton.elim (f a).toCLM 0, norm_zero]
    positivity
  · letI := h
    exact MathlibAnnex.CStarAlgebra.norm_apply_le_four
      (positiveUnitalMapOfMem f hf).toPositiveLinearMap
      (positiveUnitalMapOfMem_one f hf) a

/-- All algebraic and positivity equations defining the family are closed
in the product of weak operator topologies. -/
theorem isClosed_positiveUnitalMapSet :
    IsClosed (positiveUnitalMapSet (A := A) (H := H)) := by
  simp only [positiveUnitalMapSet, setOf_and, setOf_forall]
  refine (isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_iInter fun c => isClosed_iInter fun a =>
    isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine (isClosed_eq (by fun_prop) continuous_const).inter ?_
  exact isClosed_iInter fun a => isClosed_iInter fun _ha =>
    (isClosed_wot_nonneg (H := H)).preimage (continuous_apply (A := fun _ : A => H →WOT[ℂ] H) a)

/-- The family is compact without separability of the source or target. -/
theorem isCompact_positiveUnitalMapSet :
    IsCompact (positiveUnitalMapSet (A := A) (H := H)) :=
  (isCompact_pi_infinite (fun a : A => isCompact_wot_norm_le (H := H) (4 * ‖a‖))).of_isClosed_subset isClosed_positiveUnitalMapSet
      (fun _ hf a => norm_le_four_of_mem_positiveUnitalMapSet hf a)

/-- Real convex combinations preserve positivity, the unit and complex
linearity. The ambient linear space itself has the product WOT topology. -/
theorem convex_positiveUnitalMapSet :
    Convex ℝ (positiveUnitalMapSet (A := A) (H := H)) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    change r • f (a + b) + s • g (a + b) =
      (r • f a + s • g a) + (r • f b + s • g b)
    rw [hf.1, hg.1, smul_add, smul_add]
    abel
  · intro c a
    change r • f (c • a) + s • g (c • a) = c • (r • f a + s • g a)
    rw [hf.2.1, hg.2.1, smul_add, smul_comm r c, smul_comm s c]
  · change r • f 1 + s • g 1 = 1
    rw [hf.2.2.1, hg.2.2.1]
    apply ContinuousLinearMapWOT.toCLM_injective
    change r • _ + s • _ = _
    rw [← add_smul, hrs, one_smul]
    rfl
  · intro a ha
    change 0 ≤ r • (f a).toCLM + s • (g a).toCLM
    exact add_nonneg (smul_nonneg hr (hf.2.2.2 a ha))
      (smul_nonneg hs (hg.2.2.2 a ha))

/-- Every family of positive unital maps has a pointwise-WOT cluster point
along any nontrivial filter. The limit is again an actual positive unital map. -/
theorem exists_mapClusterPt_positiveUnitalMapSet
    {ι : Type w} (l : Filter ι) [l.NeBot]
    (P : ι → A →P[ℂ] (H →L[ℂ] H)) (hP : ∀ i, P i 1 = 1) :
    ∃ f ∈ positiveUnitalMapSet (A := A) (H := H),
      MapClusterPt f l (fun i a => ContinuousLinearMapWOT.ofCLM (P i a)) := by
  apply isCompact_positiveUnitalMapSet.exists_mapClusterPt
  rw [Filter.le_principal_iff, Filter.mem_map]
  exact Filter.Eventually.of_forall (fun i => mem_positiveUnitalMapSet (P i) (hP i))

/-- The positive unital maps with values in a specified von Neumann
algebra, prescribed restriction, and the two-sided bimodule identities. -/
def positiveBimoduleExtensionSet (D : StarSubalgebra ℂ A)
    (M : VonNeumannAlgebra H) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) :
    Set (A → (H →WOT[ℂ] H)) :=
  {f | f ∈ positiveUnitalMapSet (A := A) (H := H) ∧
    (∀ a : A, (f a).toCLM ∈ M) ∧
    (∀ d : D, f (d : A) = ContinuousLinearMapWOT.ofCLM (sigma d : H →L[ℂ] H)) ∧
    ∀ (d e : D) (a : A), f ((d : A) * a * (e : A)) =
      ContinuousLinearMapWOT.ofCLM (sigma d : H →L[ℂ] H) * f a *
        ContinuousLinearMapWOT.ofCLM (sigma e : H →L[ℂ] H)}

/-- Range restriction gives an actual positive continuous map into the
specified algebra with its original norm, not merely a formal family. -/
def positiveBimoduleExtensionOfMem
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (f : A → (H →WOT[ℂ] H)) (hf : f ∈ positiveBimoduleExtensionSet D M sigma) :
    A →P[ℂ] M.toStarSubalgebra :=
  PositiveContinuousLinearMap.mk₀
    ((positiveUnitalMapOfMem f hf.1).toContinuousLinearMap.codRestrict
      M.toStarSubalgebra.toSubalgebra.toSubmodule (fun a => hf.2.1 a))
    (fun a ha => hf.1.2.2.2 a ha)

@[simp]
theorem positiveBimoduleExtensionOfMem_apply_coe
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (f : A → (H →WOT[ℂ] H)) (hf : f ∈ positiveBimoduleExtensionSet D M sigma)
    (a : A) :
    (positiveBimoduleExtensionOfMem D M sigma f hf a : H →L[ℂ] H) = (f a).toCLM := rfl

@[simp]
theorem positiveBimoduleExtensionOfMem_one
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (f : A → (H →WOT[ℂ] H)) (hf : f ∈ positiveBimoduleExtensionSet D M sigma) :
    positiveBimoduleExtensionOfMem D M sigma f hf 1 = 1 :=
  Subtype.ext (congrArg ContinuousLinearMapWOT.toCLM hf.1.2.2.1)

@[simp]
theorem positiveBimoduleExtensionOfMem_restrict
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (f : A → (H →WOT[ℂ] H)) (hf : f ∈ positiveBimoduleExtensionSet D M sigma)
    (d : D) :
    positiveBimoduleExtensionOfMem D M sigma f hf (d : A) = sigma d :=
  Subtype.ext (congrArg ContinuousLinearMapWOT.toCLM (hf.2.2.1 d))

theorem positiveBimoduleExtensionOfMem_mul_mul
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (f : A → (H →WOT[ℂ] H)) (hf : f ∈ positiveBimoduleExtensionSet D M sigma)
    (d e : D) (a : A) :
    positiveBimoduleExtensionOfMem D M sigma f hf ((d : A) * a * (e : A)) =
      sigma d * positiveBimoduleExtensionOfMem D M sigma f hf a * sigma e :=
  Subtype.ext (congrArg ContinuousLinearMapWOT.toCLM (hf.2.2.2 d e a))

/-- An actual extension constructed by the earlier GNS-compression theorem
is a member of this family. -/
theorem mem_positiveBimoduleExtensionSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (P : A →P[ℂ] M.toStarSubalgebra) (hPone : P 1 = 1)
    (hPD : ∀ d : D, P (d : A) = sigma d)
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = sigma d * P a * sigma e) :
    (fun a => ContinuousLinearMapWOT.ofCLM (P a : H →L[ℂ] H)) ∈
      positiveBimoduleExtensionSet D M sigma := by
  let i : M.toStarSubalgebra →P[ℂ] (H →L[ℂ] H) :=
    PositiveContinuousLinearMap.mk₀ M.toStarSubalgebra.toSubalgebra.toSubmodule.subtypeL (fun _ ha => ha)
  refine ⟨mem_positiveUnitalMapSet (i.comp P) ?_, (fun a => (P a).property), ?_, ?_⟩
  · change (P 1 : H →L[ℂ] H) = 1
    rw [hPone]
    rfl
  · intro d
    exact congrArg (fun T : M.toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H)) (hPD d)
  · intro d e a
    exact congrArg (fun T : M.toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H)) (hPbi d e a)

/-- Range membership and the prescribed restriction/bimodule identities
are closed in pointwise WOT; multiplication here has fixed outer factors. -/
theorem isClosed_positiveBimoduleExtensionSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) :
    IsClosed (positiveBimoduleExtensionSet D M sigma) := by
  have hM : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ M} := by
    have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ M} =
        ContinuousLinearMapWOT.ofCLM '' (M : Set (H →L[ℂ] H)) := by
      ext T
      constructor
      · intro hT
        exact ⟨T.toCLM, hT, rfl⟩
      · rintro ⟨T, hT, rfl⟩
        exact hT
    rw [heq]
    exact M.isClosed_wot
  simp only [positiveBimoduleExtensionSet, setOf_and, setOf_forall]
  refine isClosed_positiveUnitalMapSet.inter ?_
  refine (isClosed_iInter fun a => hM.preimage (continuous_apply a)).inter ?_
  refine (isClosed_iInter fun d => isClosed_eq (by fun_prop) continuous_const).inter ?_
  exact isClosed_iInter fun d => isClosed_iInter fun e => isClosed_iInter fun a =>
    isClosed_eq (by fun_prop) (by fun_prop)

/-- The constrained extension family is compact, including the empty case. -/
theorem isCompact_positiveBimoduleExtensionSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) :
    IsCompact (positiveBimoduleExtensionSet D M sigma) :=
  isCompact_positiveUnitalMapSet.of_isClosed_subset
    (isClosed_positiveBimoduleExtensionSet D M sigma) (fun _ hf => hf.1)

/-- The actual range and the fixed bimodule identities survive real convex
combinations; no commutativity of the target is required. -/
theorem convex_positiveBimoduleExtensionSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) :
    Convex ℝ (positiveBimoduleExtensionSet D M sigma) := by
  intro f hf g hg r s hr hs hrs
  refine ⟨convex_positiveUnitalMapSet hf.1 hg.1 hr hs hrs, ?_, ?_, ?_⟩
  · intro a
    change r • (f a).toCLM + s • (g a).toCLM ∈ M
    apply M.toStarSubalgebra.add_mem
    · have h : (r : ℂ) • (f a).toCLM ∈ M.toStarSubalgebra := M.toStarSubalgebra.smul_mem (hf.2.1 a) _
      rw [Complex.coe_smul] at h
      exact h
    · have h : (s : ℂ) • (g a).toCLM ∈ M.toStarSubalgebra := M.toStarSubalgebra.smul_mem (hg.2.1 a) _
      rw [Complex.coe_smul] at h
      exact h
  · intro d
    change r • f (d : A) + s • g (d : A) = _
    rw [hf.2.2.1, hg.2.2.1]
    apply ContinuousLinearMapWOT.toCLM_injective
    change r • _ + s • _ = _
    rw [← add_smul, hrs, one_smul]
    rfl
  · intro d e a
    change r • f ((d : A) * a * (e : A)) + s • g ((d : A) * a * (e : A)) =
      ContinuousLinearMapWOT.ofCLM (sigma d : H →L[ℂ] H) * (r • f a + s • g a) *
        ContinuousLinearMapWOT.ofCLM (sigma e : H →L[ℂ] H)
    rw [hf.2.2.2, hg.2.2.2]
    apply ContinuousLinearMapWOT.toCLM_injective
    let L : H →L[ℂ] H := sigma d
    let R : H →L[ℂ] H := sigma e
    change r • (L * (f a).toCLM * R) + s • (L * (g a).toCLM * R) = L * (r • (f a).toCLM + s • (g a).toCLM) * R
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

/-- The earlier constructed positive extension proves that the family is
nonempty for an actual cyclic test configuration. The auxiliary positive
bimodule map has no normality hypothesis. -/
theorem positiveBimoduleExtensionSet_nonempty_of_positive_map
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (pi : Representation D K) (xi : K) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange (StarAlgHom.orbitMap pi xi))
    (E : (K →L[ℂ] K) →ₚ[ℂ] M.toStarSubalgebra)
    (hEpi : ∀ d : D, E (pi d) = sigma d)
    (hEbi : ∀ (d e : D) (T : K →L[ℂ] K),
      E (pi d * T * pi e) = sigma d * E T * sigma e) :
    (positiveBimoduleExtensionSet D M sigma).Nonempty := by
  letI : StarOrderedRing M.toStarSubalgebra := Subtype.starOrderedRing (𝕜 := ℂ) _
  obtain ⟨P, hPone, -, hPD, hPbi⟩ :=
    Representation.exists_positive_bimodule_extension_of_positive_map
      D pi xi hxi hcyclic sigma E hEpi hEbi
  exact ⟨fun a => ContinuousLinearMapWOT.ofCLM (P a : H →L[ℂ] H),
    mem_positiveBimoduleExtensionSet D M sigma P hPone hPD hPbi⟩

/-- A nonempty extension family has an extreme point in its actual
pointwise-WOT locally convex space. This alone makes no factor claim. -/
theorem extremePoints_positiveBimoduleExtensionSet_nonempty
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ((positiveBimoduleExtensionSet D M sigma).extremePoints ℝ).Nonempty :=
  (isCompact_positiveBimoduleExtensionSet D M sigma).extremePoints_nonempty hne

end MathlibAnnex.Analysis.CStarAlgebra
