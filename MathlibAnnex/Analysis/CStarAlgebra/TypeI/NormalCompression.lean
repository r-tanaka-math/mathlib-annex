import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveExtension
import MathlibAnnex.Analysis.VonNeumannAlgebra.Bicommutant
import MathlibAnnex.Analysis.VonNeumannAlgebra.NormalFunctional

/-!
# The normal compression induced on a generated von Neumann algebra

If compression of every represented source element lies in a specified
von Neumann algebra, the bicommutant theorem and WOT continuity put the
compression of every generated element in that same algebra. This gives an
actual positive unital map between the original von Neumann algebras.

Its preservation of directed positive suprema is proved using the existing
strong monotone convergence theorem. Source and image least upper bounds
are constructed; the statement is not only topological closure membership.
This induced map is distinct from an auxiliary positive retraction, for
which no normality is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra.Representation

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A genuine isometric compression satisfies Schwarz. The proof uses
contractivity of the adjoint on vectors and the actual quadratic forms;
it does not assert Schwarz for an arbitrary positive unital map. -/
theorem star_mul_compression_le (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (a : A) :
    star (compression rho U a) * compression rho U a ≤ compression rho U (star a * a) := by
  have hlarge : 0 ≤ compression rho U (star a * a) :=
    map_nonneg _ (star_mul_self_nonneg a)
  have hsmall : 0 ≤ star (compression rho U a) * compression rho U a :=
    star_mul_self_nonneg _
  apply sub_nonneg.mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(ContinuousLinearMap.nonneg_iff_isPositive.mp hlarge).isSelfAdjoint.sub
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hsmall).isSelfAdjoint, ?_⟩
  intro x
  have hlarge_inner :
      (inner ℂ x (compression rho U (star a * a) x)).re = ‖rho a (U x)‖ ^ 2 := by
    simp only [compression_apply, ContinuousLinearMap.comp_apply, map_mul, map_star,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (rho a (U x))
  have hsmall_inner :
      (inner ℂ x ((star (compression rho U a) * compression rho U a) x)).re =
        ‖compression rho U a x‖ ^ 2 := by
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (compression rho U a x)
  have hUadj : ‖U.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using U.norm_toContinuousLinearMap_le
  have hnorm : ‖compression rho U a x‖ ≤ ‖rho a (U x)‖ := by
    change ‖U.toContinuousLinearMap.adjoint (rho a (U x))‖ ≤ ‖rho a (U x)‖
    calc
      _ ≤ ‖U.toContinuousLinearMap.adjoint‖ * ‖rho a (U x)‖ :=
        U.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ 1 * ‖rho a (U x)‖ :=
        mul_le_mul_of_nonneg_right hUadj (norm_nonneg _)
      _ = ‖rho a (U x)‖ := one_mul _
  change 0 ≤ (inner ℂ
    ((compression rho U (star a * a) - star (compression rho U a) * compression rho U a) x) x).re
  let y := (compression rho U (star a * a) - star (compression rho U a) * compression rho U a) x
  have hsym : (inner ℂ y x).re = (inner ℂ x y).re := inner_re_symm (𝕜 := ℂ) y x
  change 0 ≤ (inner ℂ y x).re
  rw [hsym]
  dsimp only [y]
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re,
    hlarge_inner, hsmall_inner]
  nlinarith [norm_nonneg (compression rho U a x), norm_nonneg (rho a (U x))]

/-- Compression is WOT continuous, by the existing separate continuity of
composition with fixed operators. -/
theorem continuous_compression_wot (U : H →ₗᵢ[ℂ] K) :
    Continuous (fun T : K →WOT[ℂ] K =>
      (ContinuousLinearMapWOT.ofCLM U.toContinuousLinearMap.adjoint).comp
        (T.comp (ContinuousLinearMapWOT.ofCLM U.toContinuousLinearMap))) := by
  fun_prop

/-- WOT-closedness extends a source range condition to the generated
von Neumann algebra. -/
theorem compression_mem_of_mem_generated
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    {T : K →L[ℂ] K} (hT : T ∈ VonNeumannAlgebra.generated rho.range) :
    U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap) ∈ M := by
  let c : (K →WOT[ℂ] K) → (H →WOT[ℂ] H) := fun S =>
    (ContinuousLinearMapWOT.ofCLM U.toContinuousLinearMap.adjoint).comp
      (S.comp (ContinuousLinearMapWOT.ofCLM U.toContinuousLinearMap))
  have hc : Continuous c := continuous_compression_wot U
  have hsubset : ContinuousLinearMapWOT.ofCLM ''
      (rho.range : Set (K →L[ℂ] K)) ⊆
      c ⁻¹' (ContinuousLinearMapWOT.ofCLM '' (M : Set (H →L[ℂ] H))) := by
    rintro _ ⟨S, ⟨a, rfl⟩, rfl⟩
    exact ⟨compression rho U a, hsource a, rfl⟩
  have hmem := closure_minimal hsubset (M.isClosed_wot.preimage hc)
    ((VonNeumannAlgebra.mem_generated_iff_mem_wotClosure rho.range T).mp hT)
  obtain ⟨S, hS, heq⟩ := hmem
  have h : S = U.toContinuousLinearMap.adjoint ∘L (T ∘L U.toContinuousLinearMap) :=
    congrArg ContinuousLinearMapWOT.toCLM heq
  exact h ▸ hS

/-- The induced map has the actual generated algebra as its domain and
the prescribed von Neumann algebra as its codomain. -/
def generatedCompression
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M) :
    (VonNeumannAlgebra.generated rho.range).toStarSubalgebra →P[ℂ] M.toStarSubalgebra :=
  let C := compression (VonNeumannAlgebra.generated rho.range).toStarSubalgebra.subtype U
  PositiveContinuousLinearMap.mk₀
    (C.toContinuousLinearMap.codRestrict M.toStarSubalgebra.toSubalgebra.toSubmodule
      (fun T => compression_mem_of_mem_generated rho U M hsource T.property))
    (fun T hT => map_nonneg C hT)

@[simp]
theorem generatedCompression_apply_coe
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    (T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) :
    (generatedCompression rho U M hsource T : H →L[ℂ] H) =
      U.toContinuousLinearMap.adjoint ∘L
        ((T : K →L[ℂ] K) ∘L U.toContinuousLinearMap) := rfl

@[simp]
theorem generatedCompression_one
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M) :
    generatedCompression rho U M hsource 1 = 1 := by
  apply Subtype.ext
  exact compression_one (VonNeumannAlgebra.generated rho.range).toStarSubalgebra.subtype U

/-- Schwarz for the actual induced map on the full generated algebra. -/
theorem star_mul_generatedCompression_le
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    (T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) :
    star (generatedCompression rho U M hsource T) * generatedCompression rho U M hsource T ≤
      generatedCompression rho U M hsource (star T * T) :=
  star_mul_compression_le (VonNeumannAlgebra.generated rho.range).toStarSubalgebra.subtype U T

/-- On represented source elements, the induced map is the original
compression, as an equality in the ambient operator algebra. -/
@[simp]
theorem generatedCompression_generator_coe
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M) (a : A) :
    (generatedCompression rho U M hsource
      ⟨rho a, VonNeumannAlgebra.subset_generated rho.range ⟨a, rfl⟩⟩ : H →L[ℂ] H) =
        compression rho U a := rfl

/-- The induced map is bimodular over any represented common-unit
subalgebra intertwined by the isometry. The middle element ranges over the
entire generated algebra, not only over the original represented range. -/
theorem generatedCompression_mul_mul
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hU : ∀ (d : D) x, U ((sigma d : H →L[ℂ] H) x) = rho (d : A) (U x))
    (d e : D) (T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) :
    generatedCompression rho U M hsource
      (⟨rho (d : A), VonNeumannAlgebra.subset_generated rho.range ⟨(d : A), rfl⟩⟩ * T *
        ⟨rho (e : A), VonNeumannAlgebra.subset_generated rho.range ⟨(e : A), rfl⟩⟩) =
      sigma d * generatedCompression rho U M hsource T * sigma e := by
  let pi : D →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.comp sigma
  have hinter : StarAlgHom.Intertwines pi (rho.comp D.subtype)
      U.toContinuousLinearMap := by
    intro b
    ext x
    exact hU b x
  have hleft (b : D) (y : K) :
      U.toContinuousLinearMap.adjoint (rho (b : A) y) =
        (sigma b : H →L[ℂ] H) (U.toContinuousLinearMap.adjoint y) :=
    congrArg (fun S : K →L[ℂ] H => S y) (hinter.adjoint b)
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change U.toContinuousLinearMap.adjoint
      (rho (d : A) ((T : K →L[ℂ] K) (rho (e : A) (U x)))) =
    (sigma d : H →L[ℂ] H)
      (U.toContinuousLinearMap.adjoint ((T : K →L[ℂ] K) (U ((sigma e : H →L[ℂ] H) x))))
  rw [hleft, ← hU e x]

/-- Construct both least upper bounds and prove their equality under the
induced positive map, for an arbitrary directed positive bounded set. -/
theorem exists_isLUB_image_generatedCompression
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    (s : Set (VonNeumannAlgebra.generated rho.range).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s) :
    ∃ T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra,
      0 ≤ T ∧ IsLUB s T ∧
        IsLUB (generatedCompression rho U M hsource '' s)
          (generatedCompression rho U M hsource T) := by
  letI : Nonempty s := hne.to_subtype
  letI : IsDirected s (· ≤ ·) := hdir.isDirectedOrder
  obtain ⟨T, hTpos, hTlub, hTlim⟩ :=
    (VonNeumannAlgebra.generated rho.range).exists_isLUB_stronglyConverges
      s hne hdir hpos hbdd
  let E := generatedCompression rho U M hsource
  let g : s → (H →L[ℂ] H) := fun a => (E (a :
    (VonNeumannAlgebra.generated rho.range).toStarSubalgebra) : H →L[ℂ] H)
  have hgmono : Monotone g := fun _ _ hab => (OrderHomClass.mono E) hab
  have hglim : ContinuousLinearMap.StronglyConverges g atTop (E T : H →L[ℂ] H) := by
    intro x
    exact U.toContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp
      (hTlim (U x))
  have hglub := ContinuousLinearMap.isLUB_of_stronglyConverges_of_monotone hgmono hglim
  refine ⟨T, hTpos, hTlub, ?_⟩
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact hglub.1 ⟨⟨a, ha⟩, rfl⟩
  · intro b hb
    apply hglub.2
    rintro _ ⟨a, rfl⟩
    exact hb ⟨a, a.property, rfl⟩

/-- Preservation also holds for any specified source least upper bound;
its existence need not be supplied to the preceding construction. -/
theorem isLUB_image_generatedCompression
    (rho : Representation A K) (U : H →ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (hsource : ∀ a : A, compression rho U a ∈ M)
    (s : Set (VonNeumannAlgebra.generated rho.range).toStarSubalgebra)
    (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hpos : ∀ a ∈ s, 0 ≤ a) (hbdd : BddAbove s)
    {T : (VonNeumannAlgebra.generated rho.range).toStarSubalgebra} (hT : IsLUB s T) :
    IsLUB (generatedCompression rho U M hsource '' s)
      (generatedCompression rho U M hsource T) := by
  obtain ⟨S, _hSpos, hS, hES⟩ :=
    exists_isLUB_image_generatedCompression rho U M hsource s hne hdir hpos hbdd
  exact (hS.unique hT) ▸ hES

end MathlibAnnex.Analysis.CStarAlgebra.Representation
