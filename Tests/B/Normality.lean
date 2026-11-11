import MathlibAnnex.Analysis.CStarAlgebra.Enveloping.Normality

/-!
Typed consumers of actual directed suprema and their preservation.
The submitted examples are checked as direct consumers in the combined local build.
The algebra, represented Hilbert space, and family index have independent
universes. No separability, faithful action, unital source, or nontriviality
instance is imposed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open Filter Set Topology
open scoped CStarAlgebra InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.NormalityConsumers

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem at_vector {X V : Type*} {P L J C : X → Prop} {W : X → V → Prop}
    (w : ∃ a, P a ∧ L a ∧ J a ∧ C a ∧ ∀ v, W a v) (v : V) :
    ∃ a, L a ∧ J a ∧ W a v := by
  obtain ⟨a, _, hl, hj, _, hw⟩ := w
  exact ⟨a, hl, hj, hw v⟩

private theorem lub_pair {X : Type*} {P L J R : X → Prop}
    (w : ∃ a, P a ∧ L a ∧ J a ∧ R a) : ∃ a, L a ∧ J a :=
  ⟨w.choose, w.choose_spec.2.1, w.choose_spec.2.2.1⟩

private theorem lub_pair_sSup {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    [OrderSupSet X] [OrderSupSet Y] (f : X → Y) (s : Set X) {P R : X → Prop}
    (w : ∃ a, P a ∧ IsLUB s a ∧ IsLUB (f '' s) (f a) ∧ R a) :
    IsLUB s (sSup s) ∧ IsLUB (f '' s) (sSup (f '' s)) := by
  obtain ⟨a, _, hl, hj, _⟩ := w
  exact ⟨hl.isLUB_sSup, hj.isLUB_sSup⟩

/-- Existence is consumed before preservation: both actual LUBs and the
target vector limit are obtained from one source witness. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) (x : H) :
    ∃ T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra,
      IsLUB s T ∧
      IsLUB (envelopingRepresentationExtension pi hnd '' s)
        (envelopingRepresentationExtension pi hnd T) ∧
      Tendsto (fun a : s =>
        (envelopingRepresentationExtension pi hnd
          (a : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) : H →L[ℂ] H) x)
        atTop (𝓝 ((envelopingRepresentationExtension pi hnd T : H →L[ℂ] H) x)) := by
  exact at_vector (exists_isLUB_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd) x

/-- The actual `sSup` operations are consumed together with proofs that
they are LUBs, and the literal equality between the two chosen suprema. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
      OrderSupSet.choose 0
    letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
      OrderSupSet.choose 0
    IsLUB s (sSup s) ∧
      IsLUB (envelopingRepresentationExtension pi hnd '' s)
        (sSup (envelopingRepresentationExtension pi hnd '' s)) ∧
      envelopingRepresentationExtension pi hnd (sSup s) =
        sSup (envelopingRepresentationExtension pi hnd '' s) := by
  letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
    OrderSupSet.choose 0
  letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
    OrderSupSet.choose 0
  have h := lub_pair_sSup (envelopingRepresentationExtension pi hnd) s
    (exists_isLUB_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd)
  exact ⟨h.1, h.2, envelopingRepresentationExtension_sSup pi hnd s hne hdir hpos hbdd⟩

/-- A supplied LUB is preserved because the theorem's constructed LUB is
unique; it is not an additional existence premise for the preceding API. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    (s : Set (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s)
    (T : (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra) (hT : IsLUB s T) :
    IsLUB (envelopingRepresentationExtension pi hnd '' s)
      (envelopingRepresentationExtension pi hnd T) :=
  isLUB_image_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd T hT

/-- Families can be indexed by an arbitrary independent universe without
an order structure on the index type. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    {ι : Type w} [Nonempty ι]
    (f : ι → (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hdir : Directed (· ≤ ·) f) (hpos : ∀ i, 0 ≤ f i)
    (hbdd : BddAbove (Set.range f)) :
    letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
      OrderSupSet.choose 0
    letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
      OrderSupSet.choose 0
    envelopingRepresentationExtension pi hnd (⨆ i, f i) =
      ⨆ i, envelopingRepresentationExtension pi hnd (f i) :=
  envelopingRepresentationExtension_iSup pi hnd f hdir hpos hbdd

/-- In particular, an arbitrary monotone directed net has the required
supremum identity; no sequential reduction is used. -/
example (pi : NonUnitalCStarRepresentation A H) (hnd : pi.IsNondegenerate)
    {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (f : ι → (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra)
    (hmono : Monotone f) (hpos : ∀ i, 0 ≤ f i) (hbdd : BddAbove (Set.range f)) :
    letI : OrderSupSet (envelopingVonNeumannAlgebra (A := A)).toStarSubalgebra :=
      OrderSupSet.choose 0
    letI : OrderSupSet (VonNeumannAlgebra.generated pi.unitization.range).toStarSubalgebra :=
      OrderSupSet.choose 0
    envelopingRepresentationExtension pi hnd (⨆ i, f i) =
      ⨆ i, envelopingRepresentationExtension pi hnd (f i) :=
  envelopingRepresentationExtension_iSup pi hnd f hmono.directed_le hpos hbdd

section SpectralOrder

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-- The source order instances can be supplied by the standard spectral
order of any nonunital C⋆-algebra; they impose no extra algebraic hypothesis. -/
example (pi : NonUnitalCStarRepresentation B H) (hnd : pi.IsNondegenerate) :
    letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
    ∀ (s : Set (envelopingVonNeumannAlgebra (A := B)).toStarSubalgebra),
      s.Nonempty → DirectedOn (· ≤ ·) s → (∀ a ∈ s, 0 ≤ a) → BddAbove s →
      ∃ T : (envelopingVonNeumannAlgebra (A := B)).toStarSubalgebra,
        IsLUB s T ∧ IsLUB (envelopingRepresentationExtension pi hnd '' s)
          (envelopingRepresentationExtension pi hnd T) := by
  letI : PartialOrder B := _root_.CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := _root_.CStarAlgebra.spectralOrderedRing B
  intro s hne hdir hpos hbdd
  exact lub_pair (exists_isLUB_envelopingRepresentationExtension pi hnd s hne hdir hpos hbdd)

end SpectralOrder

end MathlibAnnex.Analysis.CStarAlgebra.NormalityConsumers
