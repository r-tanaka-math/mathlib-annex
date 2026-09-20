import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Extending a unitary on a closed subspace

A unitary on a closed subspace is extended by the identity on its orthogonal
complement.  This avoids imposing finite dimensionality on the ambient
Hilbert space; only the subspace needs an orthogonal projection.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace LinearIsometryEquiv

variable {𝕜 E F E' F' : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- The `L²` product of two linear isometric equivalences. -/
noncomputable def l2ProdCongr (e : E ≃ₗᵢ[𝕜] E') (f : F ≃ₗᵢ[𝕜] F') :
    WithLp 2 (E × F) ≃ₗᵢ[𝕜] WithLp 2 (E' × F') where
  toLinearEquiv :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).trans
      ((e.toLinearEquiv.prodCongr f.toLinearEquiv).trans
        (WithLp.linearEquiv 2 𝕜 (E' × F')).symm)
  norm_map' x := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖e x.fst‖ ^ 2 + ‖f x.snd‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
    rw [e.norm_map, f.norm_map]

@[simp] theorem l2ProdCongr_fst (e : E ≃ₗᵢ[𝕜] E') (f : F ≃ₗᵢ[𝕜] F')
    (x : WithLp 2 (E × F)) : (l2ProdCongr e f x).fst = e x.fst := rfl

@[simp] theorem l2ProdCongr_snd (e : E ≃ₗᵢ[𝕜] E') (f : F ≃ₗᵢ[𝕜] F')
    (x : WithLp 2 (E × F)) : (l2ProdCongr e f x).snd = f x.snd := rfl

end LinearIsometryEquiv

namespace Submodule

variable {𝕜 E : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Extend a unitary of a complemented Hilbert subspace by the identity on
the orthogonal complement.  The ambient space may be infinite dimensional. -/
noncomputable def extendUnitary (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (U : K ≃ₗᵢ[𝕜] K) : E ≃ₗᵢ[𝕜] E :=
  K.orthogonalDecomposition |>.trans
    (LinearIsometryEquiv.l2ProdCongr U (LinearIsometryEquiv.refl 𝕜 Kᗮ) |>.trans
      K.orthogonalDecomposition.symm)

/-- The extension agrees with the original unitary on the subspace. -/
@[simp] theorem extendUnitary_apply_of_mem (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : K ≃ₗᵢ[𝕜] K) {x : E} (hx : x ∈ K) :
    K.extendUnitary U x = (U ⟨x, hx⟩ : K) := by
  have hp : K.orthogonalProjectionOnto x = (⟨x, hx⟩ : K) := by
    simpa using K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩
  have hs : K.starProjection x = x := K.starProjection_eq_self_iff.mpr hx
  simp [extendUnitary, orthogonalDecomposition_apply, hp, hs]

/-- Extending an involutive unitary by the identity on the orthogonal
complement remains involutive on the whole ambient Hilbert space. -/
theorem extendUnitary_apply_twice (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : K ≃ₗᵢ[𝕜] K)
    (hU : ∀ x, U (U x) = x) (x : E) :
    K.extendUnitary U (K.extendUnitary U x) = x := by
  let D := K.orthogonalDecomposition
  let P := LinearIsometryEquiv.l2ProdCongr U
    (LinearIsometryEquiv.refl 𝕜 Kᗮ)
  change D.symm (P (D (D.symm (P (D x))))) = x
  rw [D.apply_symm_apply]
  have hPP : P (P (D x)) = D x := by
    apply (WithLp.equiv 2 (K × Kᗮ)).injective
    apply Prod.ext
    · simp [P, hU]
    · simp [P]
  rw [hPP, D.symm_apply_apply]

/-- Pointwise formula for extension by the identity on the orthogonal
complement. -/
theorem extendUnitary_apply (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : K ≃ₗᵢ[𝕜] K) (x : E) :
    K.extendUnitary U x =
      (U (K.orthogonalProjectionOnto x) : E) +
        (x - K.starProjection x) := by
  simp [extendUnitary, orthogonalDecomposition_apply,
    K.orthogonalProjectionOnto_orthogonal]

/-- The displacement of an extended unitary is supported on the subspace
where the original unitary acts. -/
theorem extendUnitary_sub_mem (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : K ≃ₗᵢ[𝕜] K) (x : E) :
    K.extendUnitary U x - x ∈ K := by
  rw [K.extendUnitary_apply]
  rw [show (U (K.orthogonalProjectionOnto x) : E) +
      (x - K.starProjection x) - x =
      (U (K.orthogonalProjectionOnto x) : E) - K.starProjection x by abel]
  exact Submodule.sub_mem K (U (K.orthogonalProjectionOnto x)).prop
    (K.starProjection_apply_mem x)

theorem range_extendUnitary_sub_id_le (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (U : K ≃ₗᵢ[𝕜] K) :
    LinearMap.range ((K.extendUnitary U).toLinearMap - LinearMap.id) ≤ K := by
  rintro y ⟨x, rfl⟩
  change K.extendUnitary U x - x ∈ K
  exact K.extendUnitary_sub_mem U x

/-- If the active subspace is finite dimensional, the displacement of its
unitary extension has finite-dimensional range. -/
theorem finiteDimensional_range_extendUnitary_sub_id (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [FiniteDimensional 𝕜 K]
    (U : K ≃ₗᵢ[𝕜] K) :
    FiniteDimensional 𝕜
      (LinearMap.range ((K.extendUnitary U).toLinearMap - LinearMap.id)) :=
  Submodule.finiteDimensional_of_le (K.range_extendUnitary_sub_id_le U)

end Submodule
