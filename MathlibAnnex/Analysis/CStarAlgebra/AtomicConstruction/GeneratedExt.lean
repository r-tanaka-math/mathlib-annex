import MathlibAnnex.Analysis.CStarAlgebra.AtomicConstruction.GeneratedReduction
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Extensionality for an actual norm-closed generated algebra

These lemmas use the defining norm closure only. They introduce no universal
completion and no claim that finite relations determine an operator norm.
-/

set_option autoImplicit false

open Topology
open scoped CStarAlgebra

namespace MathlibAnnex.CStarAlgebra.AtomicConstruction

open MathlibAnnex.Analysis.CStarAlgebra

universe u v w z
variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {J : Type w}

/-- A closed star subalgebra containing the actual source and added generators
is the whole concrete target. -/
theorem eq_top_of_source_mem_of_generator_mem
    (π : Representation A H) (U : J → H →L[ℂ] H)
    (C : StarSubalgebra ℂ (concreteTarget π U))
    (hC : IsClosed (C : Set (concreteTarget π U)))
    (hsource : ∀ a, sourceHom π U a ∈ C)
    (hgenerator : ∀ i, generator π U i ∈ C) : C = ⊤ := by
  let B : StarSubalgebra ℂ (H →L[ℂ] H) :=
    StarAlgebra.adjoin ℂ (Set.range π ∪ Set.range U)
  have hlift (x : H →L[ℂ] H) (hx : x ∈ B) :
      (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ : concreteTarget π U) ∈ C := by
    induction hx using StarAlgebra.adjoin_induction with
    | mem x hx =>
        rcases hx with ⟨a, rfl⟩ | ⟨i, rfl⟩
        · exact hsource a
        · exact hgenerator i
    | algebraMap c => exact C.algebraMap_mem c
    | add x y hx hy hxc hyc => exact C.add_mem hxc hyc
    | mul x y hx hy hxc hyc => exact C.mul_mem hxc hyc
    | star x hx hxc =>
        change star (⟨x, StarSubalgebra.le_topologicalClosure B hx⟩ :
          concreteTarget π U) ∈ C
        exact star_mem hxc
  let inclusion : B →⋆ₐ[ℂ] concreteTarget π U :=
    StarSubalgebra.inclusion (StarSubalgebra.le_topologicalClosure B)
  have hdense : DenseRange inclusion := by
    change DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure B))
    apply (denseRange_inclusion_iff _).2
    change closure (B : Set (H →L[ℂ] H)) ⊆ closure (B : Set (H →L[ℂ] H))
    exact le_rfl
  apply top_unique
  intro x _
  have hrange : Set.range inclusion ⊆ (C : Set (concreteTarget π U)) := by
    rintro _ ⟨b, rfl⟩
    exact hlift b b.property
  apply closure_minimal hrange hC
  rw [hdense.closure_range]
  exact Set.mem_univ x

/-- Two continuous star homomorphisms out of the same concrete target agree
if they agree on its displayed generators. -/
theorem starAlgHom_ext {D : Type z} [CStarAlgebra D]
    (π : Representation A H) (U : J → H →L[ℂ] H)
    (f g : concreteTarget π U →⋆ₐ[ℂ] D)
    (hsource : ∀ a, f (sourceHom π U a) = g (sourceHom π U a))
    (hgenerator : ∀ i, f (generator π U i) = g (generator π U i)) : f = g := by
  let C : StarSubalgebra ℂ (concreteTarget π U) := StarAlgHom.equalizer f g
  have hclosed : IsClosed (C : Set (concreteTarget π U)) :=
    isClosed_eq (map_continuous f) (map_continuous g)
  have htop : C = ⊤ :=
    eq_top_of_source_mem_of_generator_mem π U C hclosed hsource hgenerator
  ext a
  have ha : a ∈ C := by rw [htop]; trivial
  exact ha

/-- Intertwining two arbitrary representations, rather than requiring one of
them to be the concrete ambient inclusion. -/
theorem intertwines_of_source_of_generators
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (π : Representation A H) (U : J → H →L[ℂ] H)
    (ρ : Representation (concreteTarget π U) K)
    (σ : Representation (concreteTarget π U) L) (e : K ≃ₗᵢ[ℂ] L)
    (hsource : ∀ a, (e : K →L[ℂ] L).comp (ρ (sourceHom π U a)) =
      (σ (sourceHom π U a)).comp (e : K →L[ℂ] L))
    (hgenerator : ∀ i, (e : K →L[ℂ] L).comp (ρ (generator π U i)) =
      (σ (generator π U i)).comp (e : K →L[ℂ] L)) :
    ∀ a, (e : K →L[ℂ] L).comp (ρ a) = (σ a).comp (e : K →L[ℂ] L) := by
  let f := e.conjStarAlgEquiv.toStarAlgHom.comp ρ
  have hconj (a : concreteTarget π U)
      (ha : (e : K →L[ℂ] L).comp (ρ a) = (σ a).comp (e : K →L[ℂ] L)) :
      f a = σ a := by
    ext y
    have h := congrArg (fun T : K →L[ℂ] L ↦ T (e.symm y)) ha
    simpa [f, ContinuousLinearMap.comp_apply] using h
  have hfg : f = σ := starAlgHom_ext π U f σ
    (fun b ↦ hconj _ (hsource b)) (fun i ↦ hconj _ (hgenerator i))
  intro a
  ext x
  have h := congrArg (fun p : concreteTarget π U →⋆ₐ[ℂ] (L →L[ℂ] L) ↦
    p a (e x)) hfg
  simpa [f, ContinuousLinearMap.comp_apply] using h

end MathlibAnnex.CStarAlgebra.AtomicConstruction
