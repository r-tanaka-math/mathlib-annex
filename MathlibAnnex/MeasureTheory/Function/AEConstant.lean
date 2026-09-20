import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic

/-! Almost-everywhere constant functions and topological gluing.
The codomain is an arbitrary type. Countable gluing uses no topology or
measurability assumption on the cover members. The topological theorem only
uses positivity on nonempty open sets and the Lindelöf property of the domain.
The parent RET2 source was independently elaborated; this bounded repair
revision is qualified by the exact build evidence accompanying this source. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace MathlibAnnex

section Measurable
variable {X Y : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Equality to one constant, almost everywhere on a restricted measure. -/
def AEConstantOn (u : X → Y) (U : Set X) (c : Y) : Prop :=
  ∀ᵐ x ∂μ.restrict U, u x = c

/-- Countable local exceptional sets can be joined; an uncountable union is not used. -/
theorem aeConstantOn_of_countableCover
    {U : Set X} {u : X → Y} {c : Y}
    {ι : Type*} {V : ι → Set X} {T : Set ι}
    (hT : T.Countable) (hcover : U ⊆ ⋃ i ∈ T, V i)
    (hae : ∀ i ∈ T, AEConstantOn μ u (V i) c) :
    AEConstantOn μ u U c := by
  letI : Encodable T := hT.toEncodable
  apply ae_iff.mpr
  let bad : Set X := {x | u x ≠ c}
  have hcover' : U ⊆ ⋃ i : T, V i := by
    intro x hx
    rcases mem_iUnion₂.mp (hcover hx) with ⟨i, hiT, hxi⟩
    exact mem_iUnion.mpr ⟨⟨i, hiT⟩, hxi⟩
  have hle₁ : μ.restrict U ≤ μ.restrict (⋃ i : T, V i) :=
    Measure.restrict_mono hcover' le_rfl
  have hle₂ : μ.restrict (⋃ i : T, V i) ≤
      Measure.sum (fun i : T => μ.restrict (V i)) := Measure.restrict_iUnion_le
  have hsum : (Measure.sum (fun i : T => μ.restrict (V i))) bad = 0 := by
    rw [Measure.sum_apply_of_countable]
    exact ENNReal.tsum_eq_zero.mpr fun i => by
      simpa only [bad] using ae_iff.mp (hae i i.property)
  change (μ.restrict U) bad = 0
  exact nonpos_iff_eq_zero.mp (((hle₁.trans hle₂) bad).trans_eq hsum)
end Measurable

section Topological
variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (μ : Measure X)

/-- A local equality with explicit open-neighborhood and constant witnesses. -/
structure LocalAEConstantAt (U : Set X) (u : X → Y) (x : X) where
  neighborhood : Set X
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  neighborhood_subset : neighborhood ⊆ U
  constant : Y
  ae_eq : AEConstantOn μ u neighborhood constant

/-- Points admitting a neighborhood with a specified a.e. constant. -/
def constantRegion (U : Set X) (u : X → Y) (c : Y) : Set X :=
  {x | x ∈ U ∧ ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ AEConstantOn μ u V c}

theorem isOpen_constantRegion {U : Set X} {u : X → Y} {c : Y} :
    IsOpen (constantRegion μ U u c) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rcases hx.2 with ⟨V, hVo, hxV, hVU, hVc⟩
  refine ⟨V, ?_, hVo, hxV⟩
  intro y hy
  exact ⟨hVU hy, V, hVo, hy, hVU, hVc⟩

/-- A countable subcover is needed only for the domain, not for the entire space. -/
theorem aeConstantOn_of_everywhere_local
    {U : Set X} (hL : IsLindelof U) {u : X → Y} {c : Y}
    (hlocal : ∀ x ∈ U,
      ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ AEConstantOn μ u V c) :
    AEConstantOn μ u U c := by
  let I := {x : X // x ∈ U}
  choose V hVo hxV hVU hVc using fun x : I => hlocal x x.property
  have hcover : U ⊆ ⋃ x : I, V x := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  rcases hL.elim_countable_subcover V hVo hcover with ⟨T, hTcount, hTcover⟩
  exact aeConstantOn_of_countableCover μ hTcount hTcover (fun i _ => hVc i)

variable [μ.IsOpenPosMeasure]

/-- Positivity of an open overlap identifies its two a.e. constants. -/
theorem aeConstants_eq_of_open_overlap
    {u : X → Y} {V W : Set X} {c d : Y}
    (hVo : IsOpen V) (hWo : IsOpen W) (hVW : (V ∩ W).Nonempty)
    (hc : AEConstantOn μ u V c) (hd : AEConstantOn μ u W d) : c = d := by
  have hpos : 0 < μ (V ∩ W) := (hVo.inter hWo).measure_pos μ hVW
  have hc' : ∀ᵐ y ∂μ.restrict (V ∩ W), u y = c :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hc
  have hd' : ∀ᵐ y ∂μ.restrict (V ∩ W), u y = d :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hd
  obtain ⟨y, _, hyc, hyd⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := μ) (s := V ∩ W) (ne_of_gt hpos) (hc'.and hd')
  exact hyc.symm.trans hyd

theorem isOpen_constantRegion_compl
    {U : Set X} {u : X → Y} {c₀ : Y}
    (hlocal : ∀ x ∈ U, Nonempty (LocalAEConstantAt μ U u x)) :
    IsOpen (U \ constantRegion μ U u c₀) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  rcases hlocal x hx.1 with ⟨Lx⟩
  refine ⟨Lx.neighborhood, ?_, Lx.isOpen_neighborhood, Lx.mem_neighborhood⟩
  intro y hy
  refine ⟨Lx.neighborhood_subset hy, ?_⟩
  intro hyS
  rcases hyS.2 with ⟨W, hWo, hyW, hWU, hWc⟩
  have hconst : Lx.constant = c₀ :=
    aeConstants_eq_of_open_overlap μ Lx.isOpen_neighborhood hWo ⟨y, hy, hyW⟩ Lx.ae_eq hWc
  have hxS : x ∈ constantRegion μ U u c₀ := by
    refine ⟨Lx.neighborhood_subset Lx.mem_neighborhood, Lx.neighborhood,
      Lx.isOpen_neighborhood, Lx.mem_neighborhood, Lx.neighborhood_subset, ?_⟩
    simpa [hconst] using Lx.ae_eq
  exact hx.2 hxS

/-- Preconnectedness suffices once one nonempty constant region is specified. -/
theorem constantRegion_eq_of_preconnected
    {U : Set X} (hU : IsPreconnected U) {u : X → Y} {c₀ : Y}
    (hlocal : ∀ x ∈ U, Nonempty (LocalAEConstantAt μ U u x))
    (hne : (constantRegion μ U u c₀).Nonempty) : constantRegion μ U u c₀ = U := by
  have hSopen := isOpen_constantRegion μ (U := U) (u := u) (c := c₀)
  have hCopen := isOpen_constantRegion_compl μ (c₀ := c₀) hlocal
  have hSsub : constantRegion μ U u c₀ ⊆ U := fun _ hx => hx.1
  have hdis : Disjoint (constantRegion μ U u c₀) (U \ constantRegion μ U u c₀) :=
    Set.disjoint_left.2 fun _ hxS hxC => hxC.2 hxS
  have hcover : U ⊆ constantRegion μ U u c₀ ∪ (U \ constantRegion μ U u c₀) := by
    intro y hy
    by_cases hyS : y ∈ constantRegion μ U u c₀
    · exact Or.inl hyS
    · exact Or.inr ⟨hy, hyS⟩
  rcases hU.subset_or_subset hSopen hCopen hdis hcover with hUS | hUC
  · exact Set.Subset.antisymm hSsub hUS
  · exfalso
    rcases hne with ⟨y, hyS⟩
    exact (hUC (hSsub hyS)).2 hyS

/-- General local-to-global a.e. constancy on a connected Lindelöf domain. -/
theorem exists_aeConstantOn_of_local
    {U : Set X} (hU : IsConnected U) (hL : IsLindelof U) {u : X → Y}
    (hlocal : ∀ x ∈ U, Nonempty (LocalAEConstantAt μ U u x)) :
    ∃ c : Y, AEConstantOn μ u U c := by
  rcases hU.nonempty with ⟨x₀, hx₀⟩
  rcases hlocal x₀ hx₀ with ⟨L₀⟩
  have hxregion : x₀ ∈ constantRegion μ U u L₀.constant :=
    ⟨hx₀, L₀.neighborhood, L₀.isOpen_neighborhood, L₀.mem_neighborhood,
      L₀.neighborhood_subset, L₀.ae_eq⟩
  have hregion := constantRegion_eq_of_preconnected μ hU.2 hlocal ⟨x₀, hxregion⟩
  refine ⟨L₀.constant, aeConstantOn_of_everywhere_local μ hL ?_⟩
  intro x hx
  have hxS : x ∈ constantRegion μ U u L₀.constant := by simpa [hregion] using hx
  exact hxS.2

/-- Empty domains are permitted when the codomain has a possible constant. -/
theorem exists_aeConstantOn_of_local_preconnected [Nonempty Y]
    {U : Set X} (hU : IsPreconnected U) (hL : IsLindelof U) {u : X → Y}
    (hlocal : ∀ x ∈ U, Nonempty (LocalAEConstantAt μ U u x)) :
    ∃ c : Y, AEConstantOn μ u U c := by
  classical
  rcases U.eq_empty_or_nonempty with rfl | hne
  · exact ⟨Classical.choice ‹Nonempty Y›, by simp [AEConstantOn]⟩
  · exact exists_aeConstantOn_of_local μ ⟨hne, hU⟩ hL hlocal

end Topological
end MathlibAnnex
