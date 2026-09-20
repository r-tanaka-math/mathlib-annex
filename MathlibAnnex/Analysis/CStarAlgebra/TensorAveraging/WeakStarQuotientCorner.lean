import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.CentralKernelSection

/-!
# A constructed corner section of a weakly continuous C*-quotient

The kernel subalgebra, its two-sided ideal laws, weak closedness, support
identity, and coherent section are all constructed below. An actual
isometric predual realization supplies compact balls. The theorem does not
postulate the desired central projection or linear section.

The domain must be a C*-algebra with the explicit weak multiplication laws.
Those laws for C01's raw first-Arens Banach bidual are NOT silently inferred
from the existence of its quotient-direction represented extension.
C02 unbuilt proof-source candidate.
-/
set_option autoImplicit false
noncomputable section
open Topology

namespace MathlibAnnex.WeakStarQuotientCorner
open MathlibAnnex.WeakCompactIdealSupport MathlibAnnex.CentralKernelSection

universe u v w z
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {N : Type v} [CStarAlgebra N]
variable {X : Type w} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The actual star-closed kernel, not the kernel as a mere submodule. -/
def kernel (q : M →⋆ₐ[ℂ] N) : NonUnitalStarSubalgebra ℂ M where
  carrier := {a | q a = 0}
  zero_mem' := map_zero q
  add_mem' := by
    intro a b ha hb
    change q a = 0 at ha
    change q b = 0 at hb
    simp [ha, hb]
  mul_mem' := by
    intro a b ha hb
    change q a = 0 at ha
    change q b = 0 at hb
    simp [ha, hb]
  smul_mem' := by
    intro c a ha
    change q a = 0 at ha
    simp [ha]
  star_mem' := by
    intro a ha
    change q a = 0 at ha
    change q (star a) = 0
    simpa only [map_star, ha, star_zero]

@[simp] theorem mem_kernel (q : M →⋆ₐ[ℂ] N) (a : M) : a ∈ kernel q ↔ q a = 0 := Iff.rfl

theorem kernel_left (q : M →⋆ₐ[ℂ] N) (a x : M) (hx : x ∈ kernel q) :
    a * x ∈ kernel q := by
  change q (a * x) = 0
  change q x = 0 at hx
  simp only [map_mul, hx, mul_zero]

theorem kernel_right (q : M →⋆ₐ[ℂ] N) (x a : M) (hx : x ∈ kernel q) :
    x * a ∈ kernel q := by
  change q (x * a) = 0
  change q x = 0 at hx
  simp only [map_mul, hx, zero_mul]

/-- A weak carrier, separate from the existing normed type M. -/
def weakEquiv (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X) : M ≃ WeakDual ℂ X :=
  k.toEquiv.trans StrongDual.toWeakDual.toEquiv

@[simp] theorem weakEquiv_apply (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X) (a : M) :
    weakEquiv k a = StrongDual.toWeakDual (k a) := rfl

@[simp] theorem weakEquiv_symm_apply (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X)
    (w : WeakDual ℂ X) : (weakEquiv k).symm w = k.symm (WeakDual.toStrongDual w) := rfl

theorem continuous_weakEquiv (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X) :
    Continuous (weakEquiv k) :=
  NormedSpace.Dual.toWeakDual_continuous.comp k.continuous

/-- Weakly continuous quotient into any Hausdorff faithful carrier has a
weakly closed kernel. No norm-to-weak continuity is reversed. -/
theorem isClosed_image_kernel_weakEquiv (q : M →⋆ₐ[ℂ] N)
    (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X)
    {V : Type z} [TopologicalSpace V] [T2Space V]
    (c : N → V) (hc : Function.Injective c)
    (hq : Continuous (fun w : WeakDual ℂ X => c (q ((weakEquiv k).symm w)))) :
    IsClosed ((weakEquiv k) '' (kernel q : Set M)) := by
  have heq : ((weakEquiv k) '' (kernel q : Set M)) =
      (fun w : WeakDual ℂ X => c (q ((weakEquiv k).symm w))) ⁻¹' {c 0} := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      change q a = 0 at ha
      simpa only [Equiv.symm_apply_apply, Set.mem_preimage, Set.mem_singleton_iff, ha]
    · intro hw
      refine ⟨(weakEquiv k).symm w, ?_, (weakEquiv k).apply_symm_apply w⟩
      change c (q ((weakEquiv k).symm w)) = c 0 at hw
      exact hc hw
  rw [heq]
  exact isClosed_singleton.preimage hq

/-- An existential support theorem with no projection or section premise. -/
theorem nonempty_kernelSupport (q : M →⋆ₐ[ℂ] N)
    (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X)
    (hleft : ∀ a : M, Continuous (fun w : WeakDual ℂ X =>
      weakEquiv k (a * (weakEquiv k).symm w)))
    (hright : ∀ a : M, Continuous (fun w : WeakDual ℂ X =>
      weakEquiv k ((weakEquiv k).symm w * a)))
    {V : Type z} [TopologicalSpace V] [T2Space V]
    (c : N → V) (hc : Function.Injective c)
    (hq : Continuous (fun w : WeakDual ℂ X => c (q ((weakEquiv k).symm w)))) :
    Nonempty (KernelSupport q) := by
  obtain ⟨e, heK, henorm, hestar, hee, hecentral, hid⟩ := exists_central_identity
    (kernel q) (kernel_left q) (kernel_right q) (weakEquiv k)
    (continuous_weakEquiv k) (isCompact_predual_unitBall k)
    (isClosed_image_kernel_weakEquiv q k c hc hq) hleft hright
  exact ⟨{ e := e, in_kernel := heK, star_e := hestar, idem := hee,
           central := hecentral, identity := fun a ha => (hid a ha).1 }⟩

/-- One complete algebraic/isometric section conclusion obtained from the
constructed ideal support. Normality is not asserted merely from the norm. -/
theorem exists_isometric_corner_section (q : M →⋆ₐ[ℂ] N)
    (k : M ≃ₗᵢ[ℂ] StrongDual ℂ X)
    (hleft : ∀ a : M, Continuous (fun w : WeakDual ℂ X =>
      weakEquiv k (a * (weakEquiv k).symm w)))
    (hright : ∀ a : M, Continuous (fun w : WeakDual ℂ X =>
      weakEquiv k ((weakEquiv k).symm w * a)))
    {V : Type z} [TopologicalSpace V] [T2Space V]
    (c : N → V) (hc : Function.Injective c)
    (hq : Continuous (fun w : WeakDual ℂ X => c (q ((weakEquiv k).symm w))))
    (hball : ∀ y : N, ∃ x : M, q x = y ∧ ‖x‖ ≤ ‖y‖) :
    ∃ (p : M) (S : N →L[ℂ] M),
      star p = p ∧ p * p = p ∧ (∀ a : M, p * a = a * p) ∧
      S 1 = p ∧ (∀ y, q (S y) = y ∧ ‖S y‖ = ‖y‖) ∧
      (∀ x y, S (x * y) = S x * S y) ∧
      (∀ y, S (star y) = star (S y)) ∧
      (∀ a, S (q a) = p * a) := by
  obtain ⟨s⟩ := nonempty_kernelSupport q k hleft hright c hc hq
  exact ⟨s.projection, s.sectionCLM hball, s.projection_star, s.projection_idem,
    s.projection_central, s.value_one hball,
    fun y => ⟨s.q_value hball y, s.value_norm hball y⟩,
    s.value_mul hball, s.value_star hball, s.value_quotient hball⟩

end MathlibAnnex.WeakStarQuotientCorner
