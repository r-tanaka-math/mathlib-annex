import MathlibAnnex.Analysis.CStarAlgebra.TypeI.ExtremalExtension

/-! Typed consumers for scalar-image extremality, actual GNS compression,
and the resulting factor. These do not claim a type III test configuration
exists or that the remaining Sakai finite-projection contradiction is done. -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open MathlibAnnex.Analysis.CStarAlgebra
open scoped CStarAlgebra ComplexOrder InnerProduct

universe u v w z

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (xi : H) : Continuous (vectorEvaluation (A := A) xi) :=
  (vectorEvaluation xi).continuous

example (f : A → H →WOT[ℂ] H) (hf : f ∈ positiveUnitalMapSet)
    (xi : H) (hxi : ‖xi‖ = 1) : positiveUnitalVectorFunctional f hf xi ∈ stateSpace A :=
  positiveUnitalVectorFunctional_mem_stateSpace f hf xi hxi

example {B : Type w} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {C : Type z} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (j : A →⋆ₐ[ℂ] B) (E : B →P[ℂ] C) (q : B) (hq : 0 ≤ q)
    (hcomm : ∀ a : A, q * j a = j a * q)
    (t : ℝ) (ht : 0 < t) (hEq : E q = t • (1 : C)) :
    positiveCentralCut j E q hq hcomm t ht 1 = 1 :=
  positiveCentralCut_one j E q hq hcomm t ht hEq

variable (D : StarSubalgebra ℂ A) (M : VonNeumannAlgebra H)
variable (sigma : D →⋆ₐ[ℂ] M.toStarSubalgebra) (xi : H)

example {phi : A → ℂ} (hphi : phi ∈ positiveBimoduleVectorFunctionalSet D M sigma xi) :
    phi 1 = (‖xi‖ : ℂ) ^ 2 := by
  obtain ⟨f, hf, rfl⟩ := hphi
  rw [vectorEvaluation_apply, hf.1.2.2.1]
  exact inner_self_eq_norm_sq_to_K xi

example {phi : A → ℂ} (hphi : phi ∈ positiveBimoduleVectorFunctionalSet D M sigma 0) :
    phi = 0 := by
  obtain ⟨f, _, rfl⟩ := hphi
  funext a
  simp [vectorEvaluation_apply]

example : IsCompact (positiveBimoduleVectorFunctionalSet D M sigma xi) :=
  isCompact_positiveBimoduleVectorFunctionalSet D M sigma xi

example : Convex ℝ (positiveBimoduleVectorFunctionalSet D M sigma xi) :=
  convex_positiveBimoduleVectorFunctionalSet D M sigma xi

example (hxi : ‖xi‖ = 1) {phi : A → ℂ}
    (hphi : phi ∈ positiveBimoduleVectorFunctionalSet D M sigma xi) :
    ∃ psi : A →L[ℂ] ℂ, psi ∈ stateSpace A ∧ (psi : A → ℂ) = phi :=
  exists_state_of_mem_positiveBimoduleVectorFunctionalSet D M sigma xi hxi hphi

example (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ((positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ).Nonempty :=
  extremePoints_positiveBimoduleVectorFunctionalSet_nonempty D M sigma xi hne

example (hxi : ‖xi‖ = 1) (hne : (positiveBimoduleExtensionSet D M sigma).Nonempty) :
    ∃ (P : A →P[ℂ] M.toStarSubalgebra) (phi : A →L[ℂ] ℂ),
      P 1 = 1 ∧
      (∀ d : D, P (d : A) = sigma d) ∧
      (∀ (d e : D) (a : A), P ((d : A) * a * (e : A)) = sigma d * P a * sigma e) ∧
      phi ∈ stateSpace A ∧
      (∀ a : A, phi a = inner ℂ xi ((P a : H →L[ℂ] H) xi)) ∧
      (phi : A → ℂ) ∈ (positiveBimoduleVectorFunctionalSet D M sigma xi).extremePoints ℝ :=
  exists_extreme_positive_bimodule_vector_state D M sigma xi hxi hne

variable [IsClosed (D : Set A)] [PartialOrder D] [StarOrderedRing D]

example (hcyclic : DenseRange
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
        Representation.compression
          (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom U a =
            (P a : H →L[ℂ] H) :=
  Representation.exists_isometry_compression_eq_of_positive_bimodule
    D M sigma xi hcyclic P hPD hPbi phi hphi hcoeff

example (hM : M.IsFactor)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (hxi : ‖xi‖ = 1)
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
      (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor :=
  Representation.isFactor_gns_of_extreme_positive_bimodule_vector_state
    D M hM sigma hdense xi hxi hcyclic P hPD hPbi phi hphi hcoeff hext

example (hM : M.IsFactor)
    (hdense : ∀ T ∈ M, ContinuousLinearMapWOT.ofCLM T ∈
      closure (Set.range (fun d : D => ContinuousLinearMapWOT.ofCLM
        (sigma d : H →L[ℂ] H))))
    (hxi : ‖xi‖ = 1)
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
        (positiveLinearMapOfMemStateSpace phi hphi).gnsStarAlgHom.range).IsFactor :=
  Representation.exists_positive_bimodule_factor_extension_of_positive_map
    D M hM sigma hdense xi hxi hcyclic E hED hEbi
