/- Basic real Banach/Hilbert bundles, bounded embeddings and quantitative
Hilbert realization data. Current execution evidence is stored outside source. -/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section
namespace BanachGeometry

abbrev ScalarL2 := lp (fun _ : ℕ => ℝ) 2
abbrev ScalarC0 := ZeroAtInftyContinuousMap ℕ ℝ
abbrev HilbertPair (H : Type*) := WithLp 2 (H × ScalarL2)
abbrev C0L2 := ZeroAtInftyContinuousMap ℕ ScalarL2
abbrev L1C0L2 := lp (fun _ : ℕ => C0L2) 1

def ContainsLinearCopy (E V : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∃ (T : E →L[ℝ] V) (a : ℝ), 0 < a ∧ ∀ x, a * ‖x‖ ≤ ‖T x‖

def ContainsComplementedCopy (E V : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∃ (J : E →L[ℝ] V) (P : V →L[ℝ] E),
    P.comp J = ContinuousLinearMap.id ℝ E

def WeakNull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) : Prop :=
  ∀ f : E →L[ℝ] ℝ,
    Filter.Tendsto (fun n => f (u n)) Filter.atTop (nhds 0)

def CompletelyContinuous {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (T : E →L[ℝ] V) : Prop :=
  ∀ u : ℕ → E, WeakNull u →
    Filter.Tendsto (fun n => T (u n)) Filter.atTop (nhds 0)

structure SeparableRealBanach where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [normedSpace : NormedSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]
  [nontrivial : Nontrivial Carrier]

attribute [instance] SeparableRealBanach.normedAddCommGroup
  SeparableRealBanach.normedSpace SeparableRealBanach.completeSpace
  SeparableRealBanach.separableSpace SeparableRealBanach.nontrivial

structure SeparableRealHilbert where
  Carrier : Type
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [innerProductSpace : InnerProductSpace ℝ Carrier]
  [completeSpace : CompleteSpace Carrier]
  [separableSpace : TopologicalSpace.SeparableSpace Carrier]
  [nontrivial : Nontrivial Carrier]

attribute [instance] SeparableRealHilbert.normedAddCommGroup
  SeparableRealHilbert.innerProductSpace SeparableRealHilbert.completeSpace
  SeparableRealHilbert.separableSpace SeparableRealHilbert.nontrivial

/-- Quantitative pointed isometric realization and Hilbert bijection data; independent of a concrete free-space model. -/
structure QuantitativeHilbertData (c : ℝ) (A : SeparableRealBanach)
    (H : SeparableRealHilbert) where
  d : HilbertPair H.Carrier → A.Carrier
  d_isometry : Isometry d
  d_zero : d 0 = 0
  linearMap : A.Carrier →L[ℝ] H.Carrier
  linearMap_completelyContinuous : CompletelyContinuous linearMap
  no_c0 : ¬ ContainsLinearCopy ScalarC0 A.Carrier
  h : HilbertPair H.Carrier ≃ H.Carrier
  h_zero : h 0 = 0
  h_norm : ∀ z, ‖h z‖ = ‖z‖
  lower : ∀ z z', (1 - 4 * c) * ‖z - z'‖ ≤ ‖h z - h z'‖
  upper : ∀ z z', ‖h z - h z'‖ ≤ (1 + 4 * c) * ‖z - z'‖
  linearization : ∀ z, linearMap (d z) = h z - (WithLp.ofLp z).1

def HasQuantitativeHilbertModels : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 / 4 →
    ∃ A : SeparableRealBanach, ∃ H : SeparableRealHilbert,
      Nonempty (QuantitativeHilbertData c A H)

def AlmostIsometricAtEveryTolerance (X Y : SeparableRealBanach) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : X.Carrier ≃ Y.Carrier,
    f 0 = 0 ∧
    (∀ x x', ‖f x - f x'‖ ≤ (1 + ε) * ‖x - x'‖) ∧
    (∀ y y', ‖f.symm y - f.symm y'‖ ≤ (1 + ε) * ‖y - y'‖)

/-- Existential core only: the distance-one and concrete-complemented-copy outputs
are separate exports. -/
def ExistsAlmostIsometricNonisomorphicPair : Prop :=
  ∃ X Y : SeparableRealBanach,
    IsEmpty (X.Carrier ≃L[ℝ] Y.Carrier) ∧
    AlmostIsometricAtEveryTolerance X Y

end BanachGeometry
