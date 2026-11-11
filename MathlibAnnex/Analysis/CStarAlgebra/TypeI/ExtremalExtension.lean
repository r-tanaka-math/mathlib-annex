import MathlibAnnex.Analysis.CStarAlgebra.TypeI.PositiveBimodule
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import MathlibAnnex.Analysis.CStarAlgebra.State.Basic
import MathlibAnnex.Analysis.CStarAlgebra.TypeI.NormalCompression
import MathlibAnnex.Analysis.VonNeumannAlgebra.Factor

/-!
# Extreme vector states of positive bimodule extensions

The scalar family is the image of the actual positive bimodule extension
family under a fixed vector functional. Its topology is pointwise
convergence on the original algebra. Compactness and real convexity are
proved for this image before selecting an extreme state.

An extreme map and an extreme state in its scalar image are different
notions. This file selects the latter. Cyclicity of the prescribed test
representation identifies the selected map with the actual GNS compression.
The induced map on the generated algebra then permits normalized central
cuts within the same extension family. Extremality makes their cyclic
coefficients scalar, and the full centre is proved scalar.

The final theorem constructs a factor extension from an actual cyclic,
WOT-dense factor test representation and an actual positive bimodule map
on its bounded operators. It imposes no normality on that auxiliary map
and no separability on the ambient algebra. Existence of the required
type III test representation and the remaining finite-projection
contradiction are separate from this theorem.

The two dense-orbit coefficient recovery arguments generalize the proof
pattern in the pinned Annex `State/Irreducible.lean`; the original theorem
requires purity in the entire state space and cannot be applied to the
smaller image-state family here. Exact provenance is recorded in the
accompanying reuse ledger and notices.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProduct

namespace MathlibAnnex.Analysis.CStarAlgebra

universe u v w z

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Pointwise vector evaluation is a continuous complex-linear map from
the product of WOT operator spaces to the product of scalar spaces. -/
def vectorEvaluation (xi : H) :
    (A → (H →WOT[ℂ] H)) →L[ℂ] (A → ℂ) where
  toFun f a := inner ℂ xi (f a xi)
  map_add' := by
    intro f g
    ext a
    simp only [Pi.add_apply, ContinuousLinearMapWOT.add_apply, inner_add_right]
  map_smul' := by
    intro c f
    ext a
    simp only [Pi.smul_apply, ContinuousLinearMapWOT.smul_apply,
      inner_smul_right, RingHom.id_apply, smul_eq_mul]
  cont := by
    apply continuous_pi
    intro a
    fun_prop

@[simp]
theorem vectorEvaluation_apply (xi : H) (f : A → (H →WOT[ℂ] H)) (a : A) :
    vectorEvaluation xi f a = inner ℂ xi (f a xi) := rfl

/-- Compose the recovered positive map with the existing vector functional
of the identity representation. The result is a genuine norm-continuous
functional on the original C-star algebra. -/
def positiveUnitalVectorFunctional (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) (xi : H) : A →L[ℂ] ℂ :=
  (Representation.vectorFunctional (StarAlgHom.id ℂ (H →L[ℂ] H)) xi).comp
    (positiveUnitalMapOfMem f hf).toContinuousLinearMap

@[simp]
theorem positiveUnitalVectorFunctional_apply (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) (xi : H) (a : A) :
    positiveUnitalVectorFunctional f hf xi a = inner ℂ xi (f a xi) := rfl

/-- A unit vector gives an actual normalized positive functional. This
does not require a faithful vector state or a nonzero-target hypothesis. -/
theorem positiveUnitalVectorFunctional_mem_stateSpace
    (f : A → (H →WOT[ℂ] H))
    (hf : f ∈ positiveUnitalMapSet (A := A) (H := H)) (xi : H)
    (hxi : ‖xi‖ = 1) : positiveUnitalVectorFunctional f hf xi ∈ stateSpace A := by
  have homega := vectorFunctional_mem_stateSpace
    (StarAlgHom.id ℂ (H →L[ℂ] H)) xi hxi
  refine ⟨?_, ?_⟩
  · intro a ha
    exact homega.1 _ (map_nonneg (positiveUnitalMapOfMem f hf) ha)
  · change Representation.vectorFunctional (StarAlgHom.id ℂ (H →L[ℂ] H)) xi
      (positiveUnitalMapOfMem f hf 1) = 1
    rw [positiveUnitalMapOfMem_one]
    exact homega.2

/-- Scalar vector coefficients of the actual extension family. For a unit
vector all members are states; the ambient topology is pointwise scalar
convergence, not the operator norm on the continuous dual. -/
def positiveBimoduleVectorFunctionalSet (D : StarSubalgebra ℂ A)
    (M : VonNeumannAlgebra H) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) :
    Set (A → ℂ) :=
  vectorEvaluation xi '' positiveBimoduleExtensionSet D M sigma

/-- Every scalar member is the underlying function of a genuine state. -/
theorem exists_state_of_mem_positiveBimoduleVectorFunctionalSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) (hxi : ‖xi‖ = 1)
    {phi : A → ℂ} (hphi : phi ∈ positiveBimoduleVectorFunctionalSet D M sigma xi) :
    ∃ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A ∧ (psi : A → ℂ) = phi := by
  obtain ⟨f, hf, rfl⟩ := hphi
  exact ⟨positiveUnitalVectorFunctional f hf.1 xi,
    positiveUnitalVectorFunctional_mem_stateSpace f hf.1 xi hxi, rfl⟩

/-- The scalar image family is compact in the product scalar topology. -/
theorem isCompact_positiveBimoduleVectorFunctionalSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) :
    IsCompact (positiveBimoduleVectorFunctionalSet D M sigma xi) :=
  (isCompact_positiveBimoduleExtensionSet D M sigma).image
    (vectorEvaluation xi).continuous

/-- The scalar image family is real convex; complex linearity of vector
evaluation supplies the required real-linear map by restriction. -/
theorem convex_positiveBimoduleVectorFunctionalSet
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) :
    Convex ℝ (positiveBimoduleVectorFunctionalSet D M sigma xi) :=
  (convex_positiveBimoduleExtensionSet D M sigma).linear_image
    ((vectorEvaluation xi).restrictScalars ℝ).toLinearMap

/-- A nonempty extension family supplies an extreme point of its scalar
image, not only an extreme point of the operator-valued family. -/
theorem extremePoints_positiveBimoduleVectorFunctionalSet_nonempty
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H)
    (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ((positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ).Nonempty :=
  (isCompact_positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints_nonempty
    (hne.image (vectorEvaluation xi))

/-- Select an actual positive bimodule extension together with a genuine
state that is extreme in the scalar image family. All normalization,
restriction and bimodule equations remain attached to the selected map. -/
theorem exists_extreme_positive_bimodule_vector_state
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H) (hxi : ‖xi‖ = 1)
    (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ∃ (P : A →P[ℂ] M.toStarSubalgebra) (phi : A →L[ℂ] ℂ),
      P 1 = 1 ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      (∀ (d e : D) (a : A), P ((d : A) * a * (e : A)) = sigma d * P a * sigma e) ∧
      phi ∈ stateSpace A ∧
      (∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi)) ∧
      (phi : A → ℂ) ∈ (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ := by
  obtain ⟨phi₀, hphi₀⟩ :=
    extremePoints_positiveBimoduleVectorFunctionalSet_nonempty D M sigma xi hne
  obtain ⟨f, hf, heval⟩ := hphi₀.1
  let P := positiveBimoduleExtensionOfMem D M sigma f hf
  let phi := positiveUnitalVectorFunctional f hf.1 xi
  refine ⟨P, phi, positiveBimoduleExtensionOfMem_one D M sigma f hf,
    positiveBimoduleExtensionOfMem_restrict D M sigma f hf,
    positiveBimoduleExtensionOfMem_mul_mul D M sigma f hf,
    positiveUnitalVectorFunctional_mem_stateSpace f hf.1 xi hxi,
    (fun _ => rfl), ?_⟩
  change vectorEvaluation xi f ∈
    (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ
  rw [heval]
  exact hphi₀

section CentralCut

variable {B : Type w} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {C : Type z} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- A normalized positive central cut of a positive map. Positivity is
proved from the product of commuting positive elements; it is not a
Schwarz assumption on a general positive map. -/
def positiveCentralCut (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] C)
    (q : B) (hq : 0 ≤ q) (hcomm : ∀ a : A, q * j a = j a * q)
    (t : ℝ) (ht : 0 < t) : A →P[ℂ] C :=
  PositiveContinuousLinearMap.ofClass
    (PositiveLinearMap.mk₀ (R := ℂ)
      { toFun := fun a => t⁻¹ • E (q * j a)
        map_add' := by
          intro a b
          simp only [map_add, mul_add, smul_add]
        map_smul' := by
          intro c a
          change t⁻¹ • E (q * j (c • a)) = c • t⁻¹ • E (q * j a)
          rw [show j (c • a) = c • j a from j.toAlgHom.toLinearMap.map_smul c a,
            mul_smul_comm, map_smul, smul_comm t⁻¹ c] }
      (fun a ha => smul_nonneg (inv_pos.mpr ht).le
        (map_nonneg E (Commute.mul_nonneg hq (map_nonneg j ha) (hcomm a)))))

@[simp]
theorem positiveCentralCut_apply (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] C)
    (q : B) (hq : 0 ≤ q) (hcomm : ∀ a : A, q * j a = j a * q)
    (t : ℝ) (ht : 0 < t) (a : A) :
    positiveCentralCut j E q hq hcomm t ht a = t⁻¹ • E (q * j a) := rfl

/-- The scalar value of the central cut at the unit gives its exact
normalization. -/
theorem positiveCentralCut_one (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] C)
    (q : B) (hq : 0 ≤ q) (hcomm : ∀ a : A, q * j a = j a * q)
    (t : ℝ) (ht : 0 < t) (hEq : E q = t • (1 : C)) :
    positiveCentralCut j E q hq hcomm t ht 1 = 1 := by
  simp only [positiveCentralCut_apply, map_one, mul_one, hEq, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]

/-- The normalized cut retains the full bimodule equations over a fixed
subalgebra. The cut only needs to commute with the represented source. -/
theorem positiveCentralCut_mul_mul
    (D : StarSubalgebra ℂ A) (sigma : D →⋆ₐ[ℂ] C)
    (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] C)
    (hEbi : ∀ (d e : D) (b : B),
      E (j (d : A) * b * j (e : A)) = sigma d * E b * sigma e)
    (q : B) (hq : 0 ≤ q) (hcomm : ∀ a : A, q * j a = j a * q)
    (t : ℝ) (ht : 0 < t) (d e : D) (a : A) :
    positiveCentralCut j E q hq hcomm t ht ((d : A) * a * (e : A)) =
      sigma d * positiveCentralCut j E q hq hcomm t ht a * sigma e := by
  have hmul : q * (j (d : A) * j a * j (e : A)) =
      j (d : A) * (q * j a) * j (e : A) := by
    rw [← mul_assoc q, ← mul_assoc q, hcomm (d : A), mul_assoc (j (d : A)) q]
  simp only [positiveCentralCut_apply, map_mul, hmul, hEbi,
    mul_smul_comm, smul_mul_assoc]

/-- A central element bounded below by the unit has a strictly positive
real scalar image in a factor. Commutation is first proved on the test
algebra, then extended by WOT density using separate multiplication. -/
theorem exists_real_scalar_image_of_one_le_central
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (hM : M.IsFactor) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] M.toStarSubalgebra) (hEone : E 1 = 1)
    (hEbi : ∀ (d e : D) (b : B),
      E (j (d : A) * b * j (e : A)) = sigma d * E b * sigma e)
    (q : B) (hq : 1 ≤ q) (hcomm : ∀ b : B, b * q = q * b) :
    ∃ t : ℝ, 1 ≤ t ∧ E q = t • (1 : M.toStarSubalgebra) := by
  have hleft (d : D) : E (j (d : A) * q) = sigma d * E q := by
    simpa only [OneMemClass.coe_one, map_one, mul_one] using hEbi d 1 q
  have hright (d : D) : E (q * j (d : A)) = E q * sigma d := by
    simpa only [OneMemClass.coe_one, map_one, one_mul] using hEbi 1 d q
  have hsource (d : D) : sigma d * E q = E q * sigma d := by
    rw [← hleft, ← hright, hcomm]
  have hclosed : IsClosed {T : H →WOT[ℂ] H |
      T * ContinuousLinearMapWOT.ofCLM (E q : H →L[ℂ] H) =
        ContinuousLinearMapWOT.ofCLM (E q : H →L[ℂ] H) * T} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsubset : Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
      (sigma d : H →L[ℂ] H)) ⊆ {T : H →WOT[ℂ] H |
      T * ContinuousLinearMapWOT.ofCLM (E q : H →L[ℂ] H) =
        ContinuousLinearMapWOT.ofCLM (E q : H →L[ℂ] H) * T} := by
    rintro _ ⟨d, rfl⟩
    exact congrArg (fun b : M.toStarSubalgebra =>
      ContinuousLinearMapWOT.ofCLM (b : H →L[ℂ] H)) (hsource d)
  obtain ⟨c, hc⟩ := hM.2 (E q : H →L[ℂ] H) (E q).property (fun T hT =>
    congrArg ContinuousLinearMapWOT.toCLM
      (closure_minimal hsubset hclosed (hdense T hT)))
  let omega := vectorPositiveFunctional M.toStarSubalgebra.subtype xi hxi
  have hinner : inner ℂ xi xi = 1 := by
    simpa only [hxi, RCLike.ofReal_one, one_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) xi)
  have hge : (1 : ℂ) ≤ c := by
    calc
      1 = omega 1 := (Representation.vectorFunctional_one
        M.toStarSubalgebra.subtype hxi).symm
      _ ≤ omega (E q) := (OrderHomClass.mono omega)
        (by simpa only [hEone] using (OrderHomClass.mono E) hq)
      _ = c := by
        change inner ℂ xi ((E q : H →L[ℂ] H) xi) = c
        rw [hc]
        simp only [smul_apply, one_apply_eq_self,
          inner_smul_right, hinner, mul_one]
  refine ⟨c.re, (Complex.le_def.mp hge).1, ?_⟩
  apply Subtype.ext
  calc
    (E q : H →L[ℂ] H) = c • (1 : H →L[ℂ] H) := hc
    _ = (c.re : ℂ) • (1 : H →L[ℂ] H) :=
      congrArg (fun z : ℂ => z • (1 : H →L[ℂ] H)) (Complex.eq_re_of_ofReal_le hge)
    _ = c.re • (1 : H →L[ℂ] H) := Complex.coe_smul _ _

end CentralCut

namespace Representation

variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- A commuting operator in a cyclic representation is determined by its
single cyclic vector coefficient on the source. The two dense-orbit
arguments recover every matrix coefficient and then the operator. -/
theorem eq_smul_one_of_commuting_cyclic_coefficient
    (rho : Representation A K) (eta : K)
    (hcyclic : DenseRange (StarAlgHom.orbitMap rho eta))
    (z : K →L[ℂ] K) (hcomm : ∀ a : A, z * rho a = rho a * z)
    (c : ℂ)
    (hcoeff : ∀ a : A, inner ℂ eta (z (rho a eta)) =
      c * inner ℂ eta (rho a eta)) : z = c • (1 : K →L[ℂ] K) := by
  have hgram (a b : A) : inner ℂ (rho a eta) (z (rho b eta)) =
      inner ℂ (rho a eta) ((c • (1 : K →L[ℂ] K)) (rho b eta)) := by
    have hadj : rho (star a) = (rho a).adjoint := by
      rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    calc
      inner ℂ (rho a eta) (z (rho b eta)) =
          inner ℂ eta ((rho a).adjoint (z (rho b eta))) :=
        ((rho a).adjoint_inner_right _ _).symm
      _ = inner ℂ eta (z (rho (star a * b) eta)) := by
        rw [← hadj, map_mul]
        exact congrArg (inner ℂ eta)
          (congrArg (fun T : K →L[ℂ] K => T (rho b eta)) (hcomm (star a))).symm
      _ = c * inner ℂ eta (rho (star a * b) eta) := hcoeff (star a * b)
      _ = c * inner ℂ (rho a eta) (rho b eta) :=
        congrArg (fun t : ℂ => c * t) (vectorFunctional_star_mul rho eta a b)
      _ = inner ℂ (rho a eta) ((c • (1 : K →L[ℂ] K)) (rho b eta)) := by
        simp only [smul_apply, one_apply_eq_self,
          inner_smul_right]
  have horbit (b : A) : z (rho b eta) = (c • (1 : K →L[ℂ] K)) (rho b eta) := by
    apply ext_inner_left ℂ
    intro x
    exact hcyclic.induction_on x
      (isClosed_eq (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const)) fun a => hgram a b
  apply ContinuousLinearMap.ext
  intro x
  exact hcyclic.induction_on x
    (isClosed_eq z.continuous (c • (1 : K →L[ℂ] K)).continuous) horbit

/-- Extreme scalar image states force each member of a strictly positive
central two-piece decomposition to be scalar. The normalized cut maps are
constructed and proved to lie in the same extension family before
extremality is used. -/
theorem eq_smul_one_of_extreme_central_decomposition
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H)
    (N : VonNeumannAlgebra K) (j : A →⋆ₐ[ℂ] N.toStarSubalgebra)
    (eta : K)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (N.toStarSubalgebra.subtype.comp j) eta))
    (E : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra)
    (hEbi : ∀ (d e : D) (b : N.toStarSubalgebra),
      E (j (d : A) * b * j (e : A)) = sigma d * E b * sigma e)
    (hEcoeff : ∀ b : N.toStarSubalgebra,
      vectorFunctional M.toStarSubalgebra.subtype xi (E b) =
        vectorFunctional N.toStarSubalgebra.subtype eta b)
    (hext : (fun a : A => inner ℂ eta ((j a : K →L[ℂ] K) eta)) ∈
      (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ)
    (q r : N.toStarSubalgebra) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hqcomm : ∀ b : N.toStarSubalgebra, b * q = q * b)
    (hrcomm : ∀ b : N.toStarSubalgebra, b * r = r * b)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (hEq : E q = t • (1 : M.toStarSubalgebra))
    (hEr : E r = s • (1 : M.toStarSubalgebra))
    (hsum : q + r = (t + s) • (1 : N.toStarSubalgebra)) :
    q = (t : ℂ) • (1 : N.toStarSubalgebra) := by
  let Q := positiveCentralCut j E q hq (fun a => (hqcomm (j a)).symm) t ht
  let R := positiveCentralCut j E r hr (fun a => (hrcomm (j a)).symm) s hs
  have hQone : Q 1 = 1 := positiveCentralCut_one j E q hq _ t ht hEq
  have hRone : R 1 = 1 := positiveCentralCut_one j E r hr _ s hs hEr
  have hQbi (d e : D) (a : A) :
      Q ((d : A) * a * (e : A)) = sigma d * Q a * sigma e :=
    positiveCentralCut_mul_mul D sigma j E hEbi q hq _ t ht d e a
  have hRbi (d e : D) (a : A) :
      R ((d : A) * a * (e : A)) = sigma d * R a * sigma e :=
    positiveCentralCut_mul_mul D sigma j E hEbi r hr _ s hs d e a
  have hQD (d : D) : Q (d : A) = sigma d := by
    simpa only [OneMemClass.coe_one, mul_one, hQone, map_one] using hQbi d 1 1
  have hRD (d : D) : R (d : A) = sigma d := by
    simpa only [OneMemClass.coe_one, mul_one, hRone, map_one] using hRbi d 1 1
  let fq : A → H →WOT[ℂ] H := fun a => ContinuousLinearMapWOT.ofCLM (Q a : H →L[ℂ] H)
  let fr : A → H →WOT[ℂ] H := fun a => ContinuousLinearMapWOT.ofCLM (R a : H →L[ℂ] H)
  have hfq : fq ∈ positiveBimoduleExtensionSet D M sigma :=
    mem_positiveBimoduleExtensionSet D M sigma Q hQone hQD hQbi
  have hfr : fr ∈ positiveBimoduleExtensionSet D M sigma :=
    mem_positiveBimoduleExtensionSet D M sigma R hRone hRD hRbi
  let omega := vectorFunctional M.toStarSubalgebra.subtype xi
  let psi := vectorFunctional N.toStarSubalgebra.subtype eta
  let phi : A → ℂ := fun a => psi (j a)
  have hqeval (a : A) : vectorEvaluation xi fq a = t⁻¹ • psi (q * j a) := by
    change omega (positiveCentralCut j E q hq (fun b => (hqcomm (j b)).symm) t ht a) = _
    rw [positiveCentralCut_apply, ContinuousLinearMap.map_smul_of_tower]
    exact congrArg (fun c : ℂ => t⁻¹ • c) (hEcoeff (q * j a))
  have hreval (a : A) : vectorEvaluation xi fr a = s⁻¹ • psi (r * j a) := by
    change omega (positiveCentralCut j E r hr (fun b => (hrcomm (j b)).symm) s hs a) = _
    rw [positiveCentralCut_apply, ContinuousLinearMap.map_smul_of_tower]
    exact congrArg (fun c : ℂ => s⁻¹ • c) (hEcoeff (r * j a))
  have hts : 0 < t + s := add_pos ht hs
  have hweights : t / (t + s) + s / (t + s) = 1 := by
    rw [← add_div, div_self hts.ne']
  have hmix : (t / (t + s)) • vectorEvaluation xi fq +
      (s / (t + s)) • vectorEvaluation xi fr = phi := by
    funext a
    change (t / (t + s)) • vectorEvaluation xi fq a +
      (s / (t + s)) • vectorEvaluation xi fr a = psi (j a)
    rw [hqeval, hreval, smul_smul, smul_smul]
    have htweight : t / (t + s) * t⁻¹ = (t + s)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ ht.ne', one_mul]
    have hsweight : s / (t + s) * s⁻¹ = (t + s)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hs.ne', one_mul]
    rw [htweight, hsweight, ← smul_add, ← map_add, ← add_mul, hsum,
      smul_mul_assoc, one_mul, ContinuousLinearMap.map_smul_of_tower, smul_smul,
      inv_mul_cancel₀ hts.ne', one_smul]
  have heq : vectorEvaluation xi fq = phi := hext.2
    (mem_image_of_mem _ hfq) (mem_image_of_mem _ hfr)
    ⟨t / (t + s), s / (t + s), div_pos ht hts, div_pos hs hts, hweights, hmix⟩
  apply Subtype.ext
  apply eq_smul_one_of_commuting_cyclic_coefficient
    (N.toStarSubalgebra.subtype.comp j) eta hcyclic (q : K →L[ℂ] K)
    (fun a => congrArg Subtype.val (hqcomm (j a)).symm) (t : ℂ)
  intro a
  have hc := congrArg (fun c : ℂ => t • c) (congrFun heq a)
  rw [hqeval, smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hc
  change inner ℂ eta ((q : K →L[ℂ] K) ((j a : K →L[ℂ] K) eta)) =
    (t : ℂ) * inner ℂ eta ((j a : K →L[ℂ] K) eta)
  exact hc

/-- A state extreme in the bimodule image family gives a factor once its
actual positive extension to the represented algebra preserves the vector
functional. This theorem proves scalarity of the full centre. It does not
replace that conclusion by only a central-projection test.

Positive central elements are split into two strictly positive cuts. The
four-positive-parts decomposition is then applied inside the norm-closed
intersection with the commutant, so all four parts remain central. -/
theorem isFactor_of_extreme_bimodule_vector_state
    (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
    (hM : M.IsFactor) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (N : VonNeumannAlgebra K) (j : A →⋆ₐ[ℂ] N.toStarSubalgebra)
    (eta : K) (heta : ‖eta‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (N.toStarSubalgebra.subtype.comp j) eta))
    (E : N.toStarSubalgebra →P[ℂ] M.toStarSubalgebra) (hEone : E 1 = 1)
    (hEbi : ∀ (d e : D) (b : N.toStarSubalgebra),
      E (j (d : A) * b * j (e : A)) = sigma d * E b * sigma e)
    (hEcoeff : ∀ b : N.toStarSubalgebra,
      vectorFunctional M.toStarSubalgebra.subtype xi (E b) =
        vectorFunctional N.toStarSubalgebra.subtype eta b)
    (hext : (fun a : A => inner ℂ eta ((j a : K →L[ℂ] K) eta)) ∈
      (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ) :
    N.IsFactor := by
  have hscalar_positive (z : N.toStarSubalgebra) (hz : 0 ≤ z)
      (hzcomm : ∀ b : N.toStarSubalgebra, b * z = z * b) :
      ∃ c : ℂ, z = c • (1 : N.toStarSubalgebra) := by
    let q : N.toStarSubalgebra := z + 1
    let r : N.toStarSubalgebra := (‖z‖ + 1) • 1 - z
    have hq1 : 1 ≤ q := le_add_of_nonneg_left hz
    have hzbound : z ≤ ‖z‖ • (1 : N.toStarSubalgebra) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        IsSelfAdjoint.le_algebraMap_norm_self z hz.isSelfAdjoint
    have hr1 : 1 ≤ r := by
      apply (le_sub_iff_add_le).mpr
      calc
        (1 : N.toStarSubalgebra) + z ≤ 1 + ‖z‖ • (1 : N.toStarSubalgebra) :=
          add_le_add_right hzbound 1
        _ = (‖z‖ + 1) • (1 : N.toStarSubalgebra) := by
          rw [add_smul, one_smul, add_comm]
    have hqcomm (b : N.toStarSubalgebra) : b * q = q * b := by
      simp only [q, mul_add, add_mul, mul_one, one_mul, hzcomm b]
    have hrcomm (b : N.toStarSubalgebra) : b * r = r * b := by
      simp only [r, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul, hzcomm b]
    obtain ⟨t, ht, hEq⟩ := exists_real_scalar_image_of_one_le_central
      D M hM sigma hdense xi hxi j E hEone hEbi q hq1 hqcomm
    obtain ⟨s, hs, hEr⟩ := exists_real_scalar_image_of_one_le_central
      D M hM sigma hdense xi hxi j E hEone hEbi r hr1 hrcomm
    have hqr : q + r = (‖z‖ + 2) • (1 : N.toStarSubalgebra) := by
      change z + 1 + ((‖z‖ + 1) • 1 - z) = (‖z‖ + 2) • (1 : N.toStarSubalgebra)
      rw [add_smul, add_smul, one_smul, two_smul ℝ]
      abel
    have honeM : (1 : M.toStarSubalgebra) ≠ 0 := by
      intro h
      exact hM.1 (congrArg Subtype.val h)
    have hts : t + s = ‖z‖ + 2 := by
      apply smul_left_injective ℝ honeM
      calc
        (t + s) • (1 : M.toStarSubalgebra) = E q + E r := by
          rw [hEq, hEr, add_smul]
        _ = E (q + r) := (map_add E q r).symm
        _ = (‖z‖ + 2) • (1 : M.toStarSubalgebra) := by
          rw [hqr, PositiveContinuousLinearMap.map_smul_of_tower, hEone]
    have hqscalar := eq_smul_one_of_extreme_central_decomposition
      D M sigma xi N j eta hcyclic E hEbi hEcoeff hext
      q r (zero_le_one.trans hq1) (zero_le_one.trans hr1) hqcomm hrcomm
      t s (lt_of_lt_of_le zero_lt_one ht) (lt_of_lt_of_le zero_lt_one hs) hEq hEr
      (hqr.trans (congrArg (fun c : ℝ => c • (1 : N.toStarSubalgebra)) hts.symm))
    refine ⟨(t : ℂ) - 1, ?_⟩
    calc
      z = q - 1 := by dsimp [q]; abel
      _ = (t : ℂ) • (1 : N.toStarSubalgebra) - 1 := by rw [hqscalar]
      _ = ((t : ℂ) - 1) • (1 : N.toStarSubalgebra) := by rw [sub_smul, one_smul]
  have hone : (1 : K →L[ℂ] K) ≠ 0 := by
    intro h
    have hz : eta = 0 := congrArg (fun T : K →L[ℂ] K => T eta) h
    rw [hz, norm_zero] at heta
    exact zero_ne_one heta
  refine ⟨hone, ?_⟩
  intro z hz hzcomm
  let Z : StarSubalgebra ℂ (K →L[ℂ] K) :=
    N.toStarSubalgebra ⊓ N.commutant.toStarSubalgebra
  letI : IsClosed (Z : Set (K →L[ℂ] K)) := by
    change IsClosed ((N : Set (K →L[ℂ] K)) ∩ (N.commutant : Set (K →L[ℂ] K)))
    exact N.isClosed.inter N.commutant.isClosed
  let zz : Z := ⟨z, hz, VonNeumannAlgebra.mem_commutant_iff.mpr hzcomm⟩
  obtain ⟨y, hy, -, hdecomp⟩ := CStarAlgebra.exists_sum_four_nonneg zz
  let yN (i : Fin 4) : N.toStarSubalgebra := ⟨(y i : K →L[ℂ] K), (y i).property.1⟩
  have hycentral (i : Fin 4) (b : N.toStarSubalgebra) : b * yN i = yN i * b := by
    apply Subtype.ext
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (y i).property.2) b b.property
  have hypos (i : Fin 4) : 0 ≤ yN i := hy i
  choose c hc using fun i : Fin 4 => hscalar_positive (yN i) (hypos i) (hycentral i)
  refine ⟨∑ i : Fin 4, Complex.I ^ (i : ℕ) * c i, ?_⟩
  have hraw : z = ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (y i : K →L[ℂ] K) := by
    have he := congrArg Z.subtype hdecomp
    simp only [map_sum, map_smul, StarSubalgebra.subtype_apply] at he
    exact he
  calc
    z = ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (y i : K →L[ℂ] K) := hraw
    _ = ∑ i : Fin 4, Complex.I ^ (i : ℕ) • (c i • (1 : K →L[ℂ] K)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun T : K →L[ℂ] K => Complex.I ^ (i : ℕ) • T)
        (congrArg Subtype.val (hc i))
    _ = (∑ i : Fin 4, Complex.I ^ (i : ℕ) * c i) • (1 : K →L[ℂ] K) := by
      simp only [smul_smul, Finset.sum_smul]

/-- The prescribed vector functional and bimodule equations determine
every matrix coefficient of a positive map when the subalgebra vector is
cyclic. Hence an intertwining isometry identifies the whole map with
compression, not merely its restriction or one vector coefficient. -/
theorem compression_eq_of_cyclic_bimodule
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (tau : Representation D H) (rho : Representation A K)
    (U : H →ₗᵢ[ℂ] K) (xi : H)
    (hcyclic : DenseRange (StarAlgHom.orbitMap tau xi))
    (hU : ∀ (d : D) x, U (tau d x) = rho (d : A) (U x))
    (P : A →P[ℂ] (H →L[ℂ] H))
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = tau d * P a * tau e)
    (hcoeff : ∀ a : A,
      inner ℂ xi (P a xi) = inner ℂ (U xi) (rho a (U xi))) :
    ∀ a : A, compression rho U a = P a := by
  intro a
  have hgram (d e : D) :
      inner ℂ (tau d xi) (compression rho U a (tau e xi)) =
        inner ℂ (tau d xi) (P a (tau e xi)) := by
    calc
      inner ℂ (tau d xi) (compression rho U a (tau e xi)) =
          inner ℂ (U (tau d xi)) (rho a (U (tau e xi))) :=
        U.toContinuousLinearMap.adjoint_inner_right _ _
      _ = inner ℂ (rho (d : A) (U xi)) (rho (a * (e : A)) (U xi)) := by
        simp only [hU, map_mul, mul_apply_eq_comp]
      _ = vectorFunctional rho (U xi) (star (d : A) * (a * (e : A))) :=
        (vectorFunctional_star_mul rho (U xi) (d : A) (a * (e : A))).symm
      _ = inner ℂ xi (P (((star d : D) : A) * a * (e : A)) xi) := by
        change inner ℂ (U xi) (rho (star (d : A) * (a * (e : A))) (U xi)) = _
        rw [← mul_assoc]
        exact (hcoeff (star (d : A) * a * (e : A))).symm
      _ = inner ℂ (tau d xi) (P a (tau e xi)) := by
        rw [hPbi (star d) e a, map_star]
        change inner ℂ xi ((tau d).adjoint (P a (tau e xi))) = _
        exact (tau d).adjoint_inner_right _ _
  have honorbit (e : D) : compression rho U a (tau e xi) = P a (tau e xi) := by
    apply ext_inner_left ℂ
    intro x
    exact hcyclic.induction_on x
      (isClosed_eq (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const)) fun d => hgram d e
  apply ContinuousLinearMap.ext
  intro x
  exact hcyclic.induction_on x
    (isClosed_eq (compression rho U a).continuous (P a).continuous) fun e => honorbit e

/-- Construct the pointed isometry into the genuine GNS representation of
the vector state of a positive bimodule extension, and prove the full
compression identity. Cyclicity belongs to the specified test
representation, not to the ambient algebra. No normality, faithfulness of
the vector state, or separability is used. -/
theorem exists_isometry_compression_eq_of_positive_bimodule
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (xi : H)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (P : A →P[ℂ] M.toStarSubalgebra)
    (hPD : ∀ d : D, P (d : A) = sigma d)
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = sigma d * P a * sigma e)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi)) :
    ∃ U : H →ₗᵢ[ℂ] (positiveLinearMapOfMemStateSpace phi hphi).GNS,
      U xi = stateGNSVector phi hphi ∧
      (∀ (d : D) x, U ((sigma d : H →L[ℂ] H) x) =
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom (d : A) (U x)) ∧
      ∀ a : A,
        compression (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom U a =
          (P a : H →L[ℂ] H) := by
  let tau : Representation D H := M.toStarSubalgebra.subtype.comp sigma
  let rho := (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
  let eta := stateGNSVector phi hphi
  have hstate (d : D) : inner ℂ xi (tau d xi) =
      inner ℂ eta ((rho.comp D.subtype) d eta) := by
    calc
      inner ℂ xi (tau d xi) = inner ℂ xi ((P (d : A) : H →L[ℂ] H) xi) := by
        change inner ℂ xi ((sigma d : H →L[ℂ] H) xi) = _
        rw [hPD]
      _ = phi (d : A) := (hcoeff (d : A)).symm
      _ = inner ℂ eta ((rho.comp D.subtype) d eta) :=
        (inner_gnsStarAlgHom_stateGNSVector phi hphi (d : A)).symm
  obtain ⟨U, hpoint, hU⟩ := exists_isometry_of_eq_vector_state
    tau (rho.comp D.subtype) xi eta hcyclic hstate
  refine ⟨U, hpoint, hU, ?_⟩
  let i : M.toStarSubalgebra →P[ℂ] (H →L[ℂ] H) :=
    PositiveContinuousLinearMap.ofClass M.toStarSubalgebra.subtype
  apply compression_eq_of_cyclic_bimodule D tau rho U xi hcyclic hU (i.comp P)
  · intro d e a
    exact congrArg (fun T : M.toStarSubalgebra => (T : H →L[ℂ] H)) (hPbi d e a)
  · intro a
    change inner ℂ xi ((P a : H →L[ℂ] H) xi) = inner ℂ (U xi) (rho a (U xi))
    rw [hpoint, ← hcoeff a]
    exact (inner_gnsStarAlgHom_stateGNSVector phi hphi a).symm

/-- The selected state's genuine GNS algebra is a factor. The positive
map on this generated algebra is constructed from the pointed GNS
isometry and WOT closure; it is not an extra extension hypothesis. -/
theorem isFactor_gns_of_extreme_positive_bimodule_vector_state
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (hM : M.IsFactor)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (P : A →P[ℂ] M.toStarSubalgebra)
    (hPD : ∀ d : D, P (d : A) = sigma d)
    (hPbi : ∀ (d e : D) (a : A),
      P ((d : A) * a * (e : A)) = sigma d * P a * sigma e)
    (phi : A →L[ℂ] ℂ) (hphi : phi ∈ stateSpace A)
    (hcoeff : ∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi))
    (hext : (phi : A → ℂ) ∈
      (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ) :
    (VonNeumannAlgebra.generated
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor := by
  let rho := (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom
  let eta := stateGNSVector phi hphi
  let N := VonNeumannAlgebra.generated rho.range
  let j : A →⋆ₐ[ℂ] N.toStarSubalgebra := rho.codRestrict N.toStarSubalgebra
    (fun a => VonNeumannAlgebra.subset_generated rho.range ⟨a, rfl⟩)
  obtain ⟨U, hpoint, hU, hcompression⟩ :=
    exists_isometry_compression_eq_of_positive_bimodule
      D M sigma xi hcyclic P hPD hPbi phi hphi hcoeff
  have hsource (a : A) : compression rho U a ∈ M := by
    rw [hcompression]
    exact (P a).property
  let E := generatedCompression rho U M hsource
  apply isFactor_of_extreme_bimodule_vector_state
    D M hM sigma hdense xi hxi N j eta (norm_stateGNSVector phi hphi)
    (denseRange_gnsStarAlgHom_stateGNSVector phi hphi) E
    (generatedCompression_one rho U M hsource)
  · intro d e T
    exact generatedCompression_mul_mul rho U M hsource D sigma hU d e T
  · intro T
    change inner ℂ xi (U.toContinuousLinearMap.adjoint
      ((T : (positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
        (positiveLinearMapOfMemStateSpace phi hphi).GNS) (U xi))) =
      inner ℂ eta ((T : (positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
        (positiveLinearMapOfMemStateSpace phi hphi).GNS) eta)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (U xi) ((T : (positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
      (positiveLinearMapOfMemStateSpace phi hphi).GNS) (U xi)) = _
    rw [hpoint]
  · have hfun : (fun a : A => inner ℂ eta ((j a :
        (positiveLinearMapOfMemStateSpace phi hphi).GNS →L[ℂ]
          (positiveLinearMapOfMemStateSpace phi hphi).GNS) eta)) = (phi : A → ℂ) := by
      funext a
      exact inner_gnsStarAlgHom_stateGNSVector phi hphi a
    rwa [hfun]

/-- Starting with an actual positive bimodule map on the bounded operators
of a cyclic factor test representation, construct an ambient extension and
select a state whose genuine GNS algebra is a factor. No normality of the
input map is assumed, and no separability of the ambient algebra is used. -/
theorem exists_positive_bimodule_factor_extension_of_positive_map
    (D : StarSubalgebra ℂ A) [IsClosed (D : Set A)]
    [PartialOrder D] [StarOrderedRing D]
    (M : VonNeumannAlgebra H) (hM : M.IsFactor)
    (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (xi : H) (hxi : ‖xi‖ = 1)
    (hcyclic : DenseRange
      (StarAlgHom.orbitMap (M.toStarSubalgebra.subtype.comp sigma) xi))
    (E : (H →L[ℂ] H) →ₚ[ℂ] M.toStarSubalgebra)
    (hED : ∀ d : D, E (sigma d : H →L[ℂ] H) = sigma d)
    (hEbi : ∀ (d e : D) (T : H →L[ℂ] H),
      E ((sigma d : H →L[ℂ] H) * T * (sigma e : H →L[ℂ] H)) =
        sigma d * E T * sigma e) :
    ∃ (P : A →P[ℂ] M.toStarSubalgebra) (phi : A →L[ℂ] ℂ)
        (hphi : phi ∈ stateSpace A),
      P 1 = 1 ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      (∀ (d e : D) (a : A), P ((d : A) * a * (e : A)) = sigma d * P a * sigma e) ∧
      (∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi)) ∧
      (phi : A → ℂ) ∈ (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ ∧
      (VonNeumannAlgebra.generated
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor := by
  have hne := positiveBimoduleExtensionSet_nonempty_of_positive_map
    D M sigma (M.toStarSubalgebra.subtype.comp sigma) xi hxi hcyclic E hED hEbi
  obtain ⟨P, phi, hPone, hPD, hPbi, hphi, hcoeff, hext⟩ :=
    exists_extreme_positive_bimodule_vector_state D M sigma xi hxi hne
  exact ⟨P, phi, hphi, hPone, hPD, hPbi, hcoeff, hext,
    isFactor_gns_of_extreme_positive_bimodule_vector_state
      D M hM sigma hdense xi hxi hcyclic P hPD hPbi phi hphi hcoeff hext⟩

end Representation

end MathlibAnnex.Analysis.CStarAlgebra
