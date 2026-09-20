import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualStar
import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.ContractiveStarSampling

/-!
# The represented bidual map maps each closed ball onto the operator ball

For an irreducible unital representation, sharp simultaneous interpolation
provides a single norm-controlled source net.  Banach--Alaoglu and the
weak-star-to-WOT continuity of the explicitly constructed representation
then give a bidual preimage of every operator, with exactly its norm.

This is a genuine existence theorem, not a result taking a surjective
extension as an argument.  The chosen right inverse at the end is only a
function.  Its additivity defects are in the kernel; they are not asserted
to vanish.  Construction of a central-corner *linear* section remains a
separate obligation for the KOS averaging proof.

Controller checkpoint C01: not compiled in this chat.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace MathlibAnnex.RepresentedBidual

open MathlibAnnex.CStarAlgebra.TensorAveraging

universe u v
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- WOT-closedness of the image of a bidual ball is obtained from weak-star
compactness, not from a false norm-compactness claim. -/
theorem isClosed_wot_extension_ball
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (r : ℝ) :
    IsClosed ((fun F : WeakDual ℂ (StrongDual ℂ A) =>
        ContinuousLinearMapWOT.ofCLM
          (extension pi.toNonUnitalStarAlgHom (WeakDual.toStrongDual F))) ''
      NormedSpace.weakStarClosedBall (𝕜 := ℂ) (X := A) r) := by
  have hK : IsCompact (NormedSpace.weakStarClosedBall (𝕜 := ℂ) (X := A) r) :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℂ (StrongDual ℂ A)) r
  exact (hK.image (extension_weakStar_wotContinuous pi.toNonUnitalStarAlgHom)).isClosed

/-- The actual sharp source net also converges in the WOT. -/
theorem tendsto_contractive_sample_wot
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) :
    Tendsto (fun s : Finset H =>
      ContinuousLinearMapWOT.ofCLM (pi (contractiveStarSample pi hpi T s)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
  apply ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto.mpr
  intro xi g
  have heq : (fun s : Finset H => g (pi (contractiveStarSample pi hpi T s) xi))
      =ᶠ[atTop] (fun _ => g (T xi)) := by
    filter_upwards [contractiveStarSample_eventually_eq pi hpi T xi] with s hs
    rw [hs.1]
  exact tendsto_const_nhds.congr' heq.symm

/-- Every bounded operator has a preimage of no greater norm in the Banach
bidual under the representation constructed in `RepresentedBidual`. -/
theorem exists_extension_preimage_norm_le
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A),
      ‖F‖ ≤ ‖T‖ ∧ extension pi.toNonUnitalStarAlgHom F = T := by
  let K : Set (H →WOT[ℂ] H) :=
    (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      ContinuousLinearMapWOT.ofCLM
        (extension pi.toNonUnitalStarAlgHom (WeakDual.toStrongDual F))) ''
    NormedSpace.weakStarClosedBall (𝕜 := ℂ) (X := A) ‖T‖
  have hKclosed : IsClosed K := isClosed_wot_extension_ball pi ‖T‖
  have hmem : ∀ s : Finset H,
      ContinuousLinearMapWOT.ofCLM (pi (contractiveStarSample pi hpi T s)) ∈ K := by
    intro s
    let a := contractiveStarSample pi hpi T s
    refine ⟨StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℂ A a), ?_, ?_⟩
    · change dist (NormedSpace.inclusionInDoubleDual ℂ A a) 0 ≤ ‖T‖
      have hd : dist (NormedSpace.inclusionInDoubleDual ℂ A a) 0 =
          ‖NormedSpace.inclusionInDoubleDual ℂ A a‖ := by
        convert (dist_zero_right (NormedSpace.inclusionInDoubleDual ℂ A a)) using 1 <;> rfl
      have hn : ‖NormedSpace.inclusionInDoubleDual ℂ A a‖ = ‖a‖ := by
        convert (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℂ) (E := A)).norm_map a using 1 <;> rfl
      calc
        dist (NormedSpace.inclusionInDoubleDual ℂ A a) 0 = ‖a‖ := hd.trans hn
        _ ≤ ‖T‖ := (contractiveStarSample_spec pi hpi T s).1
    · exact congrArg ContinuousLinearMapWOT.ofCLM
        (extension_canonical pi.toNonUnitalStarAlgHom a)
  have hTmem : ContinuousLinearMapWOT.ofCLM T ∈ K :=
    hKclosed.mem_of_tendsto (tendsto_contractive_sample_wot pi hpi T)
      (Filter.Eventually.of_forall hmem)
  obtain ⟨F, hF, hFT⟩ := hTmem
  refine ⟨WeakDual.toStrongDual F, ?_, ?_⟩
  · change dist (WeakDual.toStrongDual F) 0 ≤ ‖T‖ at hF
    have hd : dist (WeakDual.toStrongDual F) 0 = ‖WeakDual.toStrongDual F‖ :=
      by convert (dist_zero_right (WeakDual.toStrongDual F)) using 1 <;> rfl
    exact hd ▸ hF
  · exact ContinuousLinearMapWOT.ofCLM_injective hFT

/-- Contractivity of the map forces the preimage bound to be equality. -/
theorem exists_extension_preimage_norm_eq
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (T : H →L[ℂ] H) :
    ∃ F : StrongDual ℂ (StrongDual ℂ A),
      ‖F‖ = ‖T‖ ∧ extension pi.toNonUnitalStarAlgHom F = T := by
  obtain ⟨F, hF, hFT⟩ := exists_extension_preimage_norm_le pi hpi T
  refine ⟨F, le_antisymm hF ?_, hFT⟩
  rw [← hFT]
  exact norm_extension_apply_le pi.toNonUnitalStarAlgHom F

theorem extension_surjective
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi) :
    Function.Surjective (extension pi.toNonUnitalStarAlgHom) := by
  intro T
  obtain ⟨F, _, hFT⟩ := exists_extension_preimage_norm_eq pi hpi T
  exact ⟨F, hFT⟩

/-- Every nonnegative-radius closed ball has exactly the expected image. -/
theorem extension_closedBall
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (r : ℝ) :
    extension pi.toNonUnitalStarAlgHom ''
      (Metric.closedBall 0 r : Set (StrongDual ℂ (StrongDual ℂ A))) =
      (Metric.closedBall 0 r : Set (H →L[ℂ] H)) := by
  ext T
  constructor
  · rintro ⟨F, hF, rfl⟩
    change dist F 0 ≤ r at hF
    change dist (extension pi.toNonUnitalStarAlgHom F) 0 ≤ r
    have hdF : dist F 0 = ‖F‖ := by
      convert (dist_zero_right F) using 1 <;> rfl
    have hdT : dist (extension pi.toNonUnitalStarAlgHom F) 0 =
        ‖extension pi.toNonUnitalStarAlgHom F‖ := by
      convert (dist_zero_right (extension pi.toNonUnitalStarAlgHom F)) using 1 <;> rfl
    calc
      dist (extension pi.toNonUnitalStarAlgHom F) 0 =
          ‖extension pi.toNonUnitalStarAlgHom F‖ := hdT
      _ ≤ ‖F‖ := norm_extension_apply_le pi.toNonUnitalStarAlgHom F
      _ = dist F 0 := hdF.symm
      _ ≤ r := hF
  · intro hT
    obtain ⟨F, hnorm, hFT⟩ := exists_extension_preimage_norm_eq pi hpi T
    refine ⟨F, ?_, hFT⟩
    change dist F 0 ≤ r
    have hdF : dist F 0 = ‖F‖ := by
      convert (dist_zero_right F) using 1 <;> rfl
    have hdT : dist T 0 = ‖T‖ := by
      convert (dist_zero_right T) using 1 <;> rfl
    change dist T 0 ≤ r at hT
    calc
      dist F 0 = ‖F‖ := hdF
      _ = ‖T‖ := hnorm
      _ = dist T 0 := hdT.symm
      _ ≤ r := hT

/-- A norm-preserving set-theoretic lift.  This is deliberately not bundled
as a linear or star homomorphism. -/
def operatorLift (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi) (T : H →L[ℂ] H) :
    StrongDual ℂ (StrongDual ℂ A) :=
  Classical.choose (exists_extension_preimage_norm_eq pi hpi T)

@[simp]
theorem norm_operatorLift (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi) (T : H →L[ℂ] H) :
    ‖operatorLift pi hpi T‖ = ‖T‖ :=
  (Classical.choose_spec (exists_extension_preimage_norm_eq pi hpi T)).1

@[simp]
theorem extension_operatorLift (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hpi : StarAlgHom.IsIrreducible pi) (T : H →L[ℂ] H) :
    extension pi.toNonUnitalStarAlgHom (operatorLift pi hpi T) = T :=
  (Classical.choose_spec (exists_extension_preimage_norm_eq pi hpi T)).2

/-- The lift's additive defect is killed by the represented map.  Replacing
this statement by exact additivity would be an unjustified central-section
assumption. -/
theorem operatorLift_add_defect_in_kernel
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (S T : H →L[ℂ] H) :
    extension pi.toNonUnitalStarAlgHom
      (operatorLift pi hpi (S + T) - (operatorLift pi hpi S + operatorLift pi hpi T)) = 0 := by
  let e := extension pi.toNonUnitalStarAlgHom
  have hs (x y : StrongDual ℂ (StrongDual ℂ A)) : e (x - y) = e x - e y := by
    convert e.map_sub x y using 1 <;> rfl
  have ha (x y : StrongDual ℂ (StrongDual ℂ A)) : e (x + y) = e x + e y := by
    convert e.map_add x y using 1 <;> rfl
  change e (operatorLift pi hpi (S + T) -
    (operatorLift pi hpi S + operatorLift pi hpi T)) = 0
  rw [hs, ha, extension_operatorLift, extension_operatorLift, extension_operatorLift, sub_self]

/-- The multiplicative defect is in the kernel, not necessarily zero in
`A**`.  This exact boundary prevents a choice-of-lifts shortcut in averaging. -/
theorem operatorLift_mul_defect_in_kernel
    (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hpi : StarAlgHom.IsIrreducible pi)
    (S T : H →L[ℂ] H) :
    extension pi.toNonUnitalStarAlgHom
      (operatorLift pi hpi (S * T) -
        arensProduct (operatorLift pi hpi S) (operatorLift pi hpi T)) = 0 := by
  let e := extension pi.toNonUnitalStarAlgHom
  have hs (x y : StrongDual ℂ (StrongDual ℂ A)) : e (x - y) = e x - e y := by
    convert e.map_sub x y using 1 <;> rfl
  change e (operatorLift pi hpi (S * T) -
    arensProduct (operatorLift pi hpi S) (operatorLift pi hpi T)) = 0
  rw [hs, extension_operatorLift, extension_arensProduct,
    extension_operatorLift, extension_operatorLift, sub_self]

end MathlibAnnex.RepresentedBidual
