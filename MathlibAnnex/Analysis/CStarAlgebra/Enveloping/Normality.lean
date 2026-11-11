import Mathlib.Order.Bounds.Basic
import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Representation
import MathlibAnnex.Analysis.VonNeumannAlgebra.NormalFunctional

/-!
# Directed suprema under the enveloping representation extension

The existing monotone convergence theorem constructs a least upper bound
in a concrete von Neumann algebra. For a WOT-continuous star homomorphism,
the image net has its own strong limit. Both nets use the source set as
their index type. Continuity and uniqueness of their scalar coefficient
limits identify the second limit with the image of the first one.

The enveloping representation extension has the required WOT continuity
by its proved all-state bidual model. Consequently its directed-supremum
statements below assume only a nondegenerate representation and a nonempty,
directed, positive, order-bounded set or family. They construct the source
and image least upper bounds, rather than assuming their existence.

The `sSup` and `iSup` statements use Mathlib's existing `OrderSupSet.choose`
locally. The preceding existence proofs ensure that its default branch is
never used for either of the sets in those statements. No complete lattice
structure on the self-adjoint part or on the whole algebra is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open Filter Set Topology
open scoped CStarAlgebra InnerProduct

universe u v w

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A WOT-continuous star homomorphism preserves an actual directed positive
supremum. The witness and its image are simultaneously strong limits of
the two nets indexed by the same source set. -/
theorem exists_isLUB_image_stronglyConverges_of_continuous_wot
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (φ : M.toStarSubalgebra →⋆ₐ[ℂ] N.toStarSubalgebra)
    (hcont : Continuous (fun T : {T : H →WOT[ℂ] H // T.toCLM ∈ M} =>
      ContinuousLinearMapWOT.ofCLM
        (φ ⟨T.val.toCLM, T.property⟩ : K →L[ℂ] K)))
    (s : Set M.toStarSubalgebra) (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : M.toStarSubalgebra, 0 ≤ T ∧ IsLUB s T ∧ IsLUB (φ '' s) (φ T) ∧
      ContinuousLinearMap.StronglyConverges
        (fun a : s => ((a : M.toStarSubalgebra) : H →L[ℂ] H)) atTop (T : H →L[ℂ] H) ∧
      ContinuousLinearMap.StronglyConverges
        (fun a : s => (φ (a : M.toStarSubalgebra) : K →L[ℂ] K))
        atTop (φ T : K →L[ℂ] K) := by
  letI : StarOrderedRing M.toStarSubalgebra := Subtype.starOrderedRing (𝕜 := ℂ) _
  letI : StarOrderedRing N.toStarSubalgebra := Subtype.starOrderedRing (𝕜 := ℂ) _
  letI : Nonempty s := hne.to_subtype
  letI : IsDirected s (· ≤ ·) := hdir.isDirectedOrder
  obtain ⟨T, hTpos, hTlub, hTlim⟩ :=
    M.exists_isLUB_stronglyConverges s hne hdir hpos hbdd
  let g : s → K →L[ℂ] K := fun a => (φ (a : M.toStarSubalgebra) : K →L[ℂ] K)
  have hgmono : Monotone g := by
    intro a b hab
    exact (OrderHomClass.mono φ) hab
  have hgpos : ∀ a, 0 ≤ g a := by
    intro a
    change (0 : N.toStarSubalgebra) ≤ φ (a : M.toStarSubalgebra)
    simpa only [map_zero] using (OrderHomClass.mono φ) (hpos a a.property)
  obtain ⟨B, hB⟩ := hbdd
  have hgbdd : BddAbove (Set.range g) := by
    refine ⟨(φ B : K →L[ℂ] K), ?_⟩
    rintro _ ⟨a, rfl⟩
    exact (OrderHomClass.mono φ) (hB a.property)
  obtain ⟨U, _hUpos, hUlub, hUlim⟩ :=
    ContinuousLinearMap.exists_isLUB_stronglyConverges_of_monotone_of_bddAbove
      g hgmono hgpos hgbdd
  have hsub : Tendsto
      (fun a : s => (⟨ContinuousLinearMapWOT.ofCLM
        ((a : M.toStarSubalgebra) : H →L[ℂ] H), a.val.property⟩ :
          {T : H →WOT[ℂ] H // T.toCLM ∈ M}))
      atTop (𝓝 (⟨ContinuousLinearMapWOT.ofCLM (T : H →L[ℂ] H), T.property⟩ :
        {T : H →WOT[ℂ] H // T.toCLM ∈ M})) :=
    tendsto_subtype_rng.mpr hTlim.tendsto_wot
  have hmap : Tendsto
      (fun a : s => ContinuousLinearMapWOT.ofCLM (g a))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (φ T : K →L[ℂ] K))) :=
    hcont.continuousAt.tendsto.comp hsub
  have hUeq : U = (φ T : K →L[ℂ] K) := by
    apply ContinuousLinearMapWOT.ofCLM_injective
    apply ContinuousLinearMapWOT.ext_inner
    intro x y
    exact tendsto_nhds_unique
      (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp
        hUlim.tendsto_wot x y)
      (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hmap x y)
  have hImage : IsLUB (φ '' s) (φ T) := by
    constructor
    · rintro _ ⟨a, ha, rfl⟩
      change (φ a : K →L[ℂ] K) ≤ (φ T : K →L[ℂ] K)
      rw [← hUeq]
      exact hUlub.1 ⟨⟨a, ha⟩, rfl⟩
    · intro C hC
      change (φ T : K →L[ℂ] K) ≤ (C : K →L[ℂ] K)
      rw [← hUeq]
      apply hUlub.2
      rintro _ ⟨a, rfl⟩
      exact hC ⟨a.val, a.property, rfl⟩
  exact ⟨T, hTpos, hTlub, hImage, hTlim, hUeq ▸ hUlim⟩

end VonNeumannAlgebra

namespace MathlibAnnex.Analysis.CStarAlgebra

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Both a directed positive set in the envelope and its image have least
upper bounds. The actual upper bound `T` and its actual image are also the
strong limits of the inclusion and image nets on the same index type. -/
theorem exists_isLUB_envelopingRepresentationExtension
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      0 ≤ T ∧ IsLUB s T ∧
      IsLUB (envelopingRepresentationExtension pi hnd '' s)
        (envelopingRepresentationExtension pi hnd T) ∧
      ContinuousLinearMap.StronglyConverges
        (fun a : s => ((a : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) :
          UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A))
        atTop (T : UniversalHilbertSpace A →L[ℂ] UniversalHilbertSpace A) ∧
      ContinuousLinearMap.StronglyConverges
        (fun a : s => (envelopingRepresentationExtension pi hnd
          (a : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) : H →L[ℂ] H))
        atTop (envelopingRepresentationExtension pi hnd T : H →L[ℂ] H) :=
  VonNeumannAlgebra.exists_isLUB_image_stronglyConverges_of_continuous_wot
    (envelopingVonNeumannAlgebra (A := A))
    (VonNeumannAlgebra.generated pi.unitization.range)
    (envelopingRepresentationExtension pi hnd)
    (continuous_envelopingRepresentationExtension_wot pi hnd) s hne hdir hpos hbdd

private theorem map_lub_from_witness {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (f : X → Y) (s : Set X) {P R : X → Prop}
    (w : ∃ x, P x ∧ IsLUB s x ∧ IsLUB (f '' s) (f x) ∧ R x)
    (x : X) (hx : IsLUB s x) : IsLUB (f '' s) (f x) := by
  obtain ⟨y, _, hy, hf, _⟩ := w
  exact hy.unique hx ▸ hf

private theorem map_sSup_from_witness {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    [OrderSupSet X] [OrderSupSet Y] (f : X → Y) (s : Set X) {P R : X → Prop}
    (w : ∃ x, P x ∧ IsLUB s x ∧ IsLUB (f '' s) (f x) ∧ R x) :
    f (sSup s) = sSup (f '' s) := by
  obtain ⟨x, _, hx, hf, _⟩ := w
  exact (congrArg f hx.sSup_eq).trans hf.sSup_eq.symm

private theorem range_lub_from_witness {X Y I : Type*} [PartialOrder X] [PartialOrder Y]
    (f : X → Y) (g : I → X) {P R : X → Prop}
    (w : ∃ x, P x ∧ IsLUB (Set.range g) x ∧ IsLUB (f '' Set.range g) (f x) ∧ R x) :
    ∃ x, P x ∧ IsLUB (Set.range g) x ∧ IsLUB (Set.range (fun i => f (g i))) (f x) := by
  obtain ⟨x, hp, hx, hf, _⟩ := w
  exact ⟨x, hp, hx, by simpa only [← Set.range_comp, Function.comp_def] using hf⟩

private theorem map_iSup_from_witness {X Y I : Type*} [PartialOrder X] [PartialOrder Y]
    [OrderSupSet X] [OrderSupSet Y] (f : X → Y) (g : I → X) {P : X → Prop}
    (w : ∃ x, P x ∧ IsLUB (Set.range g) x ∧ IsLUB (Set.range (fun i => f (g i))) (f x)) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  obtain ⟨x, _, hx, hf⟩ := w
  exact (congrArg f hx.iSup_eq).trans hf.iSup_eq.symm

/-- The extension takes every actual least upper bound of a nonempty
directed positive bounded set to the least upper bound of its image. -/
theorem isLUB_image_envelopingRepresentationExtension
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) (hT : IsLUB s T) :
    IsLUB (envelopingRepresentationExtension pi hnd '' s)
      (envelopingRepresentationExtension pi hnd T) := by
  exact map_lub_from_witness (envelopingRepresentationExtension pi hnd) s
    (exists_isLUB_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd) T hT

/-- A literal `sSup` identity for the extension. Mathlib's choice operation
is instantiated locally; existence of both least upper bounds is proved
before its correctness property is used. -/
theorem envelopingRepresentationExtension_sSup
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
      OrderSupSet.choose 0
    letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
      OrderSupSet.choose 0
    envelopingRepresentationExtension pi hnd (sSup s) =
      sSup (envelopingRepresentationExtension pi hnd '' s) := by
  letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    OrderSupSet.choose 0
  letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
    OrderSupSet.choose 0
  exact map_sSup_from_witness (envelopingRepresentationExtension pi hnd) s
    (exists_isLUB_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd)

/-- An arbitrary nonempty directed family, in an independent index
universe, has a supremum whose image is the supremum of the image family.
No order, enumeration, or countability assumption on the index is needed. -/
theorem exists_isLUB_range_envelopingRepresentationExtension
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    {ι : Type w} [Nonempty ι]
    (f : ι → (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hdir : Directed (· ≤ ·) f) (hpos : ∀ i, 0 ≤ f i)
    (hbdd : BddAbove (Set.range f)) :
    ∃ T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      0 ≤ T ∧ IsLUB (Set.range f) T ∧
      IsLUB (Set.range (fun i => envelopingRepresentationExtension pi hnd (f i)))
        (envelopingRepresentationExtension pi hnd T) := by
  have hne : (Set.range f).Nonempty := Set.range_nonempty f
  exact range_lub_from_witness (envelopingRepresentationExtension pi hnd) f
    (exists_isLUB_envelopingRepresentationExtension pi hnd (Set.range f)
      hne hdir.directedOn_range (by rintro _ ⟨i, rfl⟩; exact hpos i) hbdd)

/-- The extension preserves the actual supremum of an arbitrary nonempty
directed positive bounded family. The source and target `iSup` operations
are the standard local choices, and both are witnessed by actual LUBs. -/
theorem envelopingRepresentationExtension_iSup
    (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    {ι : Type w} [Nonempty ι]
    (f : ι → (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hdir : Directed (· ≤ ·) f) (hpos : ∀ i, 0 ≤ f i)
    (hbdd : BddAbove (Set.range f)) :
    letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
      OrderSupSet.choose 0
    letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
      OrderSupSet.choose 0
    envelopingRepresentationExtension pi hnd (⨆ i, f i) =
      ⨆ i, envelopingRepresentationExtension pi hnd (f i) := by
  letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    OrderSupSet.choose 0
  letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
    OrderSupSet.choose 0
  exact map_iSup_from_witness (envelopingRepresentationExtension pi hnd) f
    (exists_isLUB_range_envelopingRepresentationExtension pi hnd f hdir hpos hbdd)

end MathlibAnnex.Analysis.CStarAlgebra
