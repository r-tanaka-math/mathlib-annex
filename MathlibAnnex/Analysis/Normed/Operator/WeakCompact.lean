import Mathlib.Analysis.InnerProductSpace.Dual
import MathlibAnnex.Analysis.LocallyConvex.FiniteApproximation
import MathlibAnnex.Analysis.Normed.Module.Goldstine

/-!
# Weakly compact operators

This file proves Gantmacher's bidual criterion for bounded operators between
real or complex normed spaces.  Weak compactness means relative compactness
of the image of the closed unit ball in the ordinary weak topology.
-/

set_option autoImplicit false

open Bornology Topology WeakDual

namespace MathlibAnnex.WeakCompact

universe uK uX uY uZ

noncomputable section

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
variable {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedSpace ℝ Y] [IsScalarTower ℝ 𝕜 Y]
variable {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedSpace ℝ Z] [IsScalarTower ℝ 𝕜 Z]

open MathlibAnnex.FiniteApproximation

/-- The ordinary bidual map `T**`, with norm topologies on the strong
biduals. -/
def bidualMap (T : X →L[𝕜] Y) :
    StrongDual 𝕜 (StrongDual 𝕜 X) →L[𝕜]
      StrongDual 𝕜 (StrongDual 𝕜 Y) :=
  (ContinuousLinearMap.compL 𝕜 (StrongDual 𝕜 Y)
    (StrongDual 𝕜 X) 𝕜).flip (dualMap T)

@[simp]
theorem bidualMap_apply (T : X →L[𝕜] Y)
    (omega : StrongDual 𝕜 (StrongDual 𝕜 X))
    (g : StrongDual 𝕜 Y) :
    bidualMap T omega g = omega (g.comp T) := rfl

/-- Naturality of the canonical embedding into the bidual. -/
@[simp]
theorem bidualMap_canonical (T : X →L[𝕜] Y) (x : X) :
    bidualMap T (NormedSpace.inclusionInDoubleDual 𝕜 X x) =
      NormedSpace.inclusionInDoubleDual 𝕜 Y (T x) := by
  apply ContinuousLinearMap.ext
  intro g
  rfl

@[simp]
theorem bidualMap_comp (V : Y →L[𝕜] Z) (U : X →L[𝕜] Y) :
    bidualMap (V.comp U) = (bidualMap V).comp (bidualMap U) := by
  apply ContinuousLinearMap.ext
  intro omega
  apply ContinuousLinearMap.ext
  intro g
  rfl

/-- The weak image of the closed unit ball. -/
def weakBallImage (T : X →L[𝕜] Y) : Set (WeakSpace 𝕜 Y) :=
  toWeakSpace 𝕜 Y '' (T '' Metric.closedBall 0 1)

/-- A bounded operator is weakly compact when the weak closure of its unit
ball image is compact. -/
def IsWeaklyCompact (T : X →L[𝕜] Y) : Prop :=
  IsCompact (closure (weakBallImage T))

/-- The unit-ball form of the bidual range condition. -/
def MapsBidualBallToCanonical (T : X →L[𝕜] Y) : Prop :=
  ∀ omega : StrongDual 𝕜 (StrongDual 𝕜 X), ‖omega‖ ≤ 1 →
    ∃ y : Y, bidualMap T omega =
      NormedSpace.inclusionInDoubleDual 𝕜 Y y

private theorem weakStarMap_canonical (T : X →L[𝕜] Y) (x : X) :
    weakStarMap T
        (NormedSpace.inclusionInDoubleDualWeak 𝕜 X
          (toWeakSpace 𝕜 X x)) =
      NormedSpace.inclusionInDoubleDualWeak 𝕜 Y
        (toWeakSpace 𝕜 Y (T x)) := by
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.ext
  intro g
  rfl

private theorem mapsBidualBall_of_isWeaklyCompact {T : X →L[𝕜] Y}
    (hT : IsWeaklyCompact T) : MapsBidualBallToCanonical T := by
  intro omega homega
  let omegaW : WeakDual 𝕜 (StrongDual 𝕜 X) :=
    StrongDual.toWeakDual omega
  have hgold : omegaW ∈ closure
      (NormedSpace.weakStarCanonicalImage (𝕜 := 𝕜) (X := X)
        (Metric.closedBall 0 1)) := by
    apply NormedSpace.closedBall_subset_closure_weakStarCanonicalImage
    change dist omega 0 ≤ 1
    calc
      dist omega 0 = ‖omega‖ := dist_zero_right omega
      _ ≤ 1 := homega
  let jY := NormedSpace.inclusionInDoubleDualWeak 𝕜 Y
  let S := weakBallImage T
  have hmaps : Set.MapsTo (weakStarMap T)
      (NormedSpace.weakStarCanonicalImage (𝕜 := 𝕜) (X := X)
        (Metric.closedBall 0 1)) (jY '' S) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨toWeakSpace 𝕜 Y (T x), ⟨T x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    exact weakStarMap_canonical T x
  have hpush0 := mem_closure_image (weakStarMap T).continuous.continuousAt hgold
  have hpush : weakStarMap T omegaW ∈ closure (jY '' S) :=
    closure_mono hmaps.image_subset hpush0
  have hcimage : IsCompact (jY '' closure S) :=
    hT.image jY.continuous
  have hclosed : IsClosed (jY '' closure S) := hcimage.isClosed
  have hsub : closure (jY '' S) ⊆ jY '' closure S :=
    closure_minimal (Set.image_mono subset_closure) hclosed
  rcases hsub hpush with ⟨y, _, hy⟩
  refine ⟨(toWeakSpace 𝕜 Y).symm y, ?_⟩
  apply WeakDual.toStrongDual.injective
  apply ContinuousLinearMap.ext
  intro g
  have hy' := congrArg (fun q : WeakDual 𝕜 (StrongDual 𝕜 Y) ↦ q g) hy
  change omega (g.comp T) = g ((toWeakSpace 𝕜 Y).symm y)
  change g ((toWeakSpace 𝕜 Y).symm y) = omega (g.comp T) at hy'
  exact hy'.symm

private theorem isBounded_weakBallImage (T : X →L[𝕜] Y) :
    IsBounded ((toWeakSpace 𝕜 Y) ⁻¹' weakBallImage T) := by
  have hpre : (toWeakSpace 𝕜 Y) ⁻¹' weakBallImage T =
      T '' Metric.closedBall 0 1 := by
    ext y
    simp [weakBallImage]
  rw [hpre]
  exact T.lipschitz.isBounded_image Metric.isBounded_closedBall

private theorem isWeaklyCompact_of_mapsBidualBall {T : X →L[𝕜] Y}
    (hT : MapsBidualBallToCanonical T) : IsWeaklyCompact T := by
  let S := weakBallImage T
  let jY := NormedSpace.inclusionInDoubleDualWeak 𝕜 Y
  let K : Set (WeakDual 𝕜 (StrongDual 𝕜 Y)) :=
    weakStarMap T '' NormedSpace.weakStarClosedBall (𝕜 := 𝕜) (X := X) 1
  have hKcompact : IsCompact K :=
    (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 X)) 1).image
      (weakStarMap T).continuous
  have hcanon : jY '' S ⊆ K := by
    rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨NormedSpace.inclusionInDoubleDualWeak 𝕜 X
      (toWeakSpace 𝕜 X x), ?_, weakStarMap_canonical T x⟩
    change dist x 0 ≤ 1 at hx
    change dist (NormedSpace.inclusionInDoubleDual 𝕜 X x) 0 ≤ 1
    calc
      dist (NormedSpace.inclusionInDoubleDual 𝕜 X x) 0 =
          dist x 0 := by
        have hd := IsometryClass.dist_eq
          (NormedSpace.inclusionInDoubleDualLi
            (𝕜 := 𝕜) (E := X)) x 0
        change dist (NormedSpace.inclusionInDoubleDual 𝕜 X x)
          (NormedSpace.inclusionInDoubleDual 𝕜 X 0) = dist x 0 at hd
        rw [map_zero] at hd
        exact hd
      _ ≤ 1 := hx
  have hKrange : K ⊆ Set.range jY := by
    rintro _ ⟨omega, homega, rfl⟩
    have homega' : ‖WeakDual.toStrongDual omega‖ ≤ 1 := by
      change dist (WeakDual.toStrongDual omega) 0 ≤ 1 at homega
      calc
        ‖WeakDual.toStrongDual omega‖ =
            dist (WeakDual.toStrongDual omega) 0 :=
          (dist_zero_right (WeakDual.toStrongDual omega)).symm
        _ ≤ 1 := homega
    rcases hT (WeakDual.toStrongDual omega) homega' with ⟨y, hy⟩
    refine ⟨toWeakSpace 𝕜 Y y, ?_⟩
    apply WeakDual.toStrongDual.injective
    change NormedSpace.inclusionInDoubleDual 𝕜 Y y =
      bidualMap T (WeakDual.toStrongDual omega)
    exact hy.symm
  have hclosure : closure (jY '' S) ⊆ Set.range jY := by
    exact (closure_minimal hcanon hKcompact.isClosed).trans hKrange
  exact NormedSpace.isCompact_closure_of_isBounded 𝕜 Y S
    (by simpa [S] using isBounded_weakBallImage T) hclosure

/-- **Gantmacher's theorem**, in unit-ball range form. -/
theorem isWeaklyCompact_iff_mapsBidualBall (T : X →L[𝕜] Y) :
    IsWeaklyCompact T ↔ MapsBidualBallToCanonical T :=
  ⟨mapsBidualBall_of_isWeaklyCompact,
    isWeaklyCompact_of_mapsBidualBall⟩

/-- The unit-ball range condition implies the full bidual range condition. -/
theorem exists_bidualMap_eq_canonical_of_mapsBidualBall
    {T : X →L[𝕜] Y} (hT : MapsBidualBallToCanonical T)
    (omega : StrongDual 𝕜 (StrongDual 𝕜 X)) :
    ∃ y : Y, bidualMap T omega =
      NormedSpace.inclusionInDoubleDual 𝕜 Y y := by
  let r : ℝ := ‖omega‖ + 1
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let c : 𝕜 := (r⁻¹ : ℝ)
  have hc : ‖c‖ = r⁻¹ := by simp [c, abs_of_pos hr]
  have hunit : ‖c • omega‖ ≤ 1 := by
    calc
      ‖c • omega‖ ≤ ‖c‖ * ‖omega‖ :=
        ContinuousLinearMap.opNorm_smul_le c omega
      _ = r⁻¹ * ‖omega‖ := by rw [hc]
      _ = ‖omega‖ / r := by rw [div_eq_inv_mul]
      _ ≤ 1 := (div_le_one hr).2 (by dsimp [r]; linarith)
  rcases hT (c • omega) hunit with ⟨y, hy⟩
  refine ⟨(r : 𝕜) • y, ?_⟩
  have hc_mul : (r : 𝕜) * c = 1 := by
    simp [c, hr.ne']
  calc
    bidualMap T omega = (r : 𝕜) • bidualMap T (c • omega) := by
      rw [map_smul, smul_smul, hc_mul, one_smul]
    _ = (r : 𝕜) • NormedSpace.inclusionInDoubleDual 𝕜 Y y := by rw [hy]
    _ = NormedSpace.inclusionInDoubleDual 𝕜 Y ((r : 𝕜) • y) :=
      ((NormedSpace.inclusionInDoubleDual 𝕜 Y).map_smul (r : 𝕜) y).symm

/-- Gantmacher's criterion with its usual full-range statement. -/
theorem isWeaklyCompact_iff_bidual_range (T : X →L[𝕜] Y) :
    IsWeaklyCompact T ↔
      ∀ omega : StrongDual 𝕜 (StrongDual 𝕜 X),
        ∃ y : Y, bidualMap T omega =
          NormedSpace.inclusionInDoubleDual 𝕜 Y y := by
  rw [isWeaklyCompact_iff_mapsBidualBall]
  constructor
  · exact exists_bidualMap_eq_canonical_of_mapsBidualBall
  · intro h omega _
    exact h omega

/-- Banach-space reflexivity, expressed by surjectivity of the canonical
isometric embedding. -/
def IsReflexive (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕜 E)

/-- An operator factoring through a reflexive space is weakly compact. -/
theorem isWeaklyCompact_of_factorization
    (U : X →L[𝕜] Z) (V : Z →L[𝕜] Y)
    (hZ : IsReflexive (𝕜 := 𝕜) Z) :
    IsWeaklyCompact (V.comp U) := by
  rw [isWeaklyCompact_iff_bidual_range]
  intro omega
  rcases hZ (bidualMap U omega) with ⟨z, hz⟩
  refine ⟨V z, ?_⟩
  rw [bidualMap_comp, ContinuousLinearMap.comp_apply, ← hz,
    bidualMap_canonical]

/-- The dual of a reflexive Banach space is reflexive.  This is proved
directly from surjectivity of the canonical embedding, so it does not add a
reflexivity assumption for dual spaces. -/
theorem isReflexive_dual (hX : IsReflexive (𝕜 := 𝕜) X) :
    IsReflexive (𝕜 := 𝕜) (StrongDual 𝕜 X) := by
  intro Omega
  let J : X →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 X) :=
    (NormedSpace.inclusionInDoubleDualLi
      (𝕜 := 𝕜) (E := X)).toContinuousLinearMap
  let f : StrongDual 𝕜 X := Omega.comp J
  refine ⟨f, ?_⟩
  apply ContinuousLinearMap.ext
  intro q
  rcases hX q with ⟨x, hx⟩
  subst q
  rfl

/-- Postcomposition by a bounded operator preserves weak compactness. -/
theorem isWeaklyCompact_postcomp
    (T : X →L[𝕜] Y) (hT : IsWeaklyCompact T) (V : Y →L[𝕜] Z) :
    IsWeaklyCompact (V.comp T) := by
  rw [isWeaklyCompact_iff_bidual_range] at hT ⊢
  intro omega
  rcases hT omega with ⟨y, hy⟩
  refine ⟨V y, ?_⟩
  rw [bidualMap_comp, ContinuousLinearMap.comp_apply, hy,
    bidualMap_canonical]

/-- Precomposition by a bounded operator preserves weak compactness. -/
theorem isWeaklyCompact_precomp
    (T : Y →L[𝕜] Z) (hT : IsWeaklyCompact T) (U : X →L[𝕜] Y) :
    IsWeaklyCompact (T.comp U) := by
  rw [isWeaklyCompact_iff_bidual_range] at hT ⊢
  intro omega
  rcases hT (bidualMap U omega) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [bidualMap_comp, ContinuousLinearMap.comp_apply, hz]

end

section Hilbert

universe uH

variable {𝕜 : Type uK} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

private noncomputable def conjugatePullback
    (omega : StrongDual 𝕜 (StrongDual 𝕜 H)) : StrongDual 𝕜 H :=
  LinearMap.mkContinuous
    { toFun := fun y ↦ star (omega (InnerProductSpace.toDual 𝕜 H y))
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp [map_smulₛₗ, map_smul] }
    ‖omega‖ fun y ↦ by
      change ‖star (omega (InnerProductSpace.toDual 𝕜 H y))‖ ≤
        ‖omega‖ * ‖y‖
      rw [norm_star]
      exact (omega.le_opNorm _).trans_eq (by
        rw [(InnerProductSpace.toDual 𝕜 H).norm_map])

/-- Every real or complex Hilbert space is reflexive.  The proof constructs
the preimage under the canonical bidual embedding from the Riesz isometry;
reflexivity is not assumed. -/
theorem isReflexive_innerProductSpace : IsReflexive (𝕜 := 𝕜) H := by
  intro omega
  let ell : StrongDual 𝕜 H := conjugatePullback omega
  let x : H := (InnerProductSpace.toDual 𝕜 H).symm ell
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro g
  change g x = omega g
  let y : H := (InnerProductSpace.toDual 𝕜 H).symm g
  have hgy : InnerProductSpace.toDual 𝕜 H y = g :=
    (InnerProductSpace.toDual 𝕜 H).apply_symm_apply g
  have hell : InnerProductSpace.toDual 𝕜 H x = ell :=
    (InnerProductSpace.toDual 𝕜 H).apply_symm_apply ell
  calc
    g x = inner 𝕜 y x := by rw [← hgy]; rfl
    _ = star (inner 𝕜 x y) := (inner_conj_symm y x).symm
    _ = star (ell y) := by rw [← hell]; rfl
    _ = omega (InnerProductSpace.toDual 𝕜 H y) := by
      simp [ell, conjugatePullback]
    _ = omega g := by rw [hgy]

end Hilbert

end MathlibAnnex.WeakCompact
