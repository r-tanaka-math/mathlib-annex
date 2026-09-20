import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Isolated points below the continuum

A nonempty locally compact Hausdorff space of cardinality smaller than the
continuum has an isolated point.  No metrizability or countability is used.

The proof uses the existing Urysohn-based clopen-basis theorem, disjoint
binary splitting, and compactness along branches.  It constructs a set
injection from binary sequences, not a topological embedding of Cantor space.
-/

set_option autoImplicit false

open Function Set Topology TopologicalSpace
open scoped Cardinal

namespace MathlibAnnex.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A nonempty open set without isolated points contains two distinct points. -/
private theorem exists_ne_mem_of_not_isOpen_singleton
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    {s : Set X} (hs : IsOpen s) {x : X} (hx : x ∈ s) :
    ∃ y ∈ s, y ≠ x := by
  by_contra h
  have heq : s = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyx : y = x := by
        by_contra hne
        exact h ⟨y, hy, hne⟩
      exact Set.mem_singleton_iff.mpr hyx
    · exact Set.singleton_subset_iff.mpr hx
  exact hno x (heq ▸ hs)

/-- Split a nonempty clopen set into two nonempty clopen subsets. -/
private theorem exists_isClopen_subset_and_nonempty_sdiff [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    {s : Set X} (hs : IsClopen s) (hne : s.Nonempty) :
    ∃ t : Set X, IsClopen t ∧ t ⊆ s ∧ t.Nonempty ∧ (s \ t).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hyx⟩ := exists_ne_mem_of_not_isOpen_singleton hno hs.isOpen hx
  have hx' : x ∈ s ∩ ({y} : Set X)ᶜ := ⟨hx, by simpa using hyx.symm⟩
  obtain ⟨t, ht, hxt, hts⟩ :=
    hbasis.exists_subset_of_mem_open hx'
      (hs.isOpen.inter isClosed_singleton.isOpen_compl)
  refine ⟨t, ht, fun z hz => (hts hz).1, ⟨x, hxt⟩, y, hy, ?_⟩
  intro hyt
  exact (hts hyt).2 (Set.mem_singleton y)

private abbrev NonemptyClopen (X : Type u) [TopologicalSpace X] :=
  {s : Set X // IsClopen s ∧ s.Nonempty}

private theorem exists_disjoint_nonempty_clopen_subsets [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) (s : NonemptyClopen X) :
    ∃ t : Bool → NonemptyClopen X,
      (∀ b, (t b).1 ⊆ s.1) ∧ Disjoint (t false).1 (t true).1 := by
  classical
  obtain ⟨t, ht, hts, htne, hdiff⟩ := exists_isClopen_subset_and_nonempty_sdiff hbasis hno s.2.1 s.2.2
  let left : NonemptyClopen X := ⟨t, ht, htne⟩
  let right : NonemptyClopen X := ⟨s.1 \ t, by
    simpa only [sdiff_eq] using s.2.1.inter ht.compl, hdiff⟩
  refine ⟨fun b => if b then right else left, ?_, ?_⟩
  · intro b
    cases b
    · exact hts
    · exact fun _ hx => hx.1
  · change Disjoint t (s.1 \ t)
    exact Set.disjoint_left.mpr fun x hxt hx => hx.2 hxt

private noncomputable def clopenChild [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (s : NonemptyClopen X) : Bool → NonemptyClopen X :=
  Classical.choose (exists_disjoint_nonempty_clopen_subsets hbasis hno s)

private theorem clopenChild_subset [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (s : NonemptyClopen X) (b : Bool) :
    (clopenChild hbasis hno s b).1 ⊆ s.1 :=
  (Classical.choose_spec (exists_disjoint_nonempty_clopen_subsets hbasis hno s)).1 b

private theorem disjoint_clopenChild [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (s : NonemptyClopen X) :
    Disjoint (clopenChild hbasis hno s false).1
      (clopenChild hbasis hno s true).1 :=
  (Classical.choose_spec (exists_disjoint_nonempty_clopen_subsets hbasis hno s)).2

private noncomputable def clopenTree [T1Space X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X))
    (root : NonemptyClopen X) : List Bool → NonemptyClopen X
  | [] => root
  | b :: l => clopenChild hbasis hno (clopenTree hbasis hno root l) b

/-- Compactness makes every branch of a closed antitone scheme nonempty.
No metric or shrinking-diameter hypothesis is required. -/
theorem _root_.CantorScheme.nonempty_iInter_of_isCompact
    {B : Type*} (S : List B → Set X)
    (hanti : _root_.CantorScheme.Antitone S)
    (hne : ∀ l, (S l).Nonempty)
    (hcompact : IsCompact (S [])) (hclosed : ∀ l, IsClosed (S l))
    (a : ℕ → B) : (⋂ n, S (PiNat.res a n)).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => S (PiNat.res a n))
  · intro n
    simpa only [PiNat.res_succ] using hanti (PiNat.res a n) (a n)
  · intro n
    exact hne _
  · simpa using hcompact
  · intro n
    exact hclosed _

/-- A compact Hausdorff space with a clopen basis and no isolated points
contains a set-theoretic copy of the binary sequence space. -/
theorem exists_injective_nat_bool_of_isTopologicalBasis_clopens
    [CompactSpace X] [T2Space X] [Nonempty X]
    (hbasis : IsTopologicalBasis {s : Set X | IsClopen s})
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    ∃ f : (ℕ → Bool) → X, Injective f := by
  classical
  let root : NonemptyClopen X := ⟨Set.univ, isClopen_univ, Set.univ_nonempty⟩
  let S : List Bool → Set X := fun l => (clopenTree hbasis hno root l).1
  have hanti : _root_.CantorScheme.Antitone S := by
    intro l b
    exact clopenChild_subset hbasis hno (clopenTree hbasis hno root l) b
  have hdis : _root_.CantorScheme.Disjoint S := by
    intro l a b hab
    have hd := disjoint_clopenChild hbasis hno (clopenTree hbasis hno root l)
    cases a <;> cases b
    · exact (hab rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hab rfl).elim
  have hne (l) : (S l).Nonempty := (clopenTree hbasis hno root l).2.2
  have hc (l) : IsClosed (S l) := (clopenTree hbasis hno root l).2.1.isClosed
  have hbranch (a : ℕ → Bool) : (⋂ n, S (PiNat.res a n)).Nonempty :=
    CantorScheme.nonempty_iInter_of_isCompact S hanti hne (hc []).isCompact hc a
  let f : (ℕ → Bool) → X :=
    fun a => (_root_.CantorScheme.inducedMap S).2 ⟨a, hbranch a⟩
  refine ⟨f, ?_⟩
  intro a b hab
  have hsub := hdis.map_injective hab
  exact congrArg Subtype.val hsub

/-- A nonempty compact Hausdorff space smaller than the continuum has an
isolated point. -/
theorem exists_isOpen_singleton_of_compactSpace_of_cardinalMk_lt_continuum
    [CompactSpace X] [T2Space X] [Nonempty X]
    (hcard : #X < Cardinal.continuum) : ∃ x : X, IsOpen ({x} : Set X) := by
  classical
  by_contra h
  have hno : ∀ x : X, ¬ IsOpen ({x} : Set X) := fun x hx => h ⟨x, hx⟩
  have hbasis :=
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum hcard
  obtain ⟨f, hf⟩ := exists_injective_nat_bool_of_isTopologicalBasis_clopens hbasis hno
  have hle := Cardinal.lift_mk_le_lift_mk_of_injective hf
  have hlarge : Cardinal.continuum ≤ #X := by
    simpa [Cardinal.mk_arrow, Cardinal.mk_bool] using hle
  exact (not_le_of_gt hcard) hlarge

/-- A nonempty locally compact Hausdorff space of cardinality below the
continuum has an isolated point. -/
theorem exists_isOpen_singleton_of_cardinalMk_lt_continuum
    [LocallyCompactSpace X] [T2Space X] [Nonempty X]
    (hcard : #X < Cardinal.continuum) : ∃ x : X, IsOpen ({x} : Set X) := by
  classical
  letI : CompletelyRegularSpace X :=
    (OnePoint.isOpenEmbedding_coe (X := X)).isEmbedding.isInducing.completelyRegularSpace
  have hbasis :=
    CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum hcard
  let x : X := Classical.choice inferInstance
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have hxint : x ∈ interior K := mem_interior_iff_mem_nhds.mpr hxK
  obtain ⟨V, hV, hxV, hVK⟩ := hbasis.exists_subset_of_mem_open hxint isOpen_interior
  have hVcompact : IsCompact V :=
    hK.of_isClosed_subset hV.isClosed (hVK.trans interior_subset)
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hVcompact
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hVcard : #V < Cardinal.continuum :=
    (Cardinal.mk_le_of_injective (Subtype.val_injective : Injective (Subtype.val : V → X))).trans_lt hcard
  obtain ⟨y, hy⟩ :=
    exists_isOpen_singleton_of_compactSpace_of_cardinalMk_lt_continuum hVcard
  refine ⟨y.1, ?_⟩
  simpa using hV.isOpen.isOpenMap_subtype_val ({y} : Set V) hy

/-- Cardinal lower bound for nonempty locally compact Hausdorff spaces
without isolated points. -/
theorem continuum_le_cardinalMk_of_not_isOpen_singleton
    [LocallyCompactSpace X] [T2Space X] [Nonempty X]
    (hno : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    Cardinal.continuum ≤ #X := by
  by_contra h
  obtain ⟨x, hx⟩ := exists_isOpen_singleton_of_cardinalMk_lt_continuum (lt_of_not_ge h)
  exact hno x hx

end MathlibAnnex.Topology
