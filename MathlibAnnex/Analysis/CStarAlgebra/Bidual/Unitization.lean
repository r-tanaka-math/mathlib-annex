import MathlibAnnex.Analysis.CStarAlgebra.Bidual.Functorial
import MathlibAnnex.Analysis.CStarAlgebra.FacialStructure.FunctionalExtension

/-!
# The bidual embedding into a unitization and non-unital C*-laws

The canonical inclusion into the unitization induces an isometry of the
literal Banach biduals. The lower norm estimate uses the existing
norm-preserving extension of arbitrary source functionals; neither states
nor positivity of those extensions is needed. The embedding preserves the
already defined Arens product and involution. Injectivity then transfers
the unital antimultiplicativity law, and isometry transfers the exact C*
norm identity, to every non-unital C*-algebra, including the zero algebra.

The target is used only to prove identities on the original bidual. It is
not substituted for that bidual, and no scalar summand is added to its
carrier or to a universal representation.
-/

set_option autoImplicit false
noncomputable section

open scoped CStarAlgebra
open MathlibAnnex.RepresentedBidual MathlibAnnex.WeakCompact
open MathlibAnnex.FiniteApproximation Topology

namespace MathlibAnnex.Analysis.CStarAlgebra.Bidual

universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]

private def inclusionCLM : A →L[ℂ] Unitization ℂ A where
  toLinearMap := (Unitization.inrNonUnitalStarAlgHom ℂ A : A →ₗ[ℂ] Unitization ℂ A)
  cont := Unitization.isometry_inr.continuous

/-- The ordinary bidual map of the canonical inclusion into the unitization. -/
def unitizationBidual :
    StrongDual ℂ (StrongDual ℂ A) →L[ℂ]
      StrongDual ℂ (StrongDual ℂ (Unitization ℂ A)) :=
  bidualMap (inclusionCLM (A := A))

@[simp]
theorem unitizationBidual_apply (F : StrongDual ℂ (StrongDual ℂ A))
    (g : StrongDual ℂ (Unitization ℂ A)) :
    unitizationBidual F g =
      F (g.comp (inclusionCLM (A := A))) :=
  rfl

/-- Evaluation against the already constructed norm-preserving extension
recovers the original functional exactly. -/
theorem unitizationBidual_eval_extension (F : StrongDual ℂ (StrongDual ℂ A))
    (f : StrongDual ℂ A) :
    unitizationBidual F (unitizationDualExtension f) = F f := by
  rw [unitizationBidual_apply]
  congr 1
  ext a
  exact unitizationDualExtension_inr f a

/-- Both norm inequalities are proved for the original operator norms. -/
@[simp]
theorem norm_unitizationBidual (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖unitizationBidual F‖ = ‖F‖ := by
  let i : A →L[ℂ] Unitization ℂ A :=
    (inclusionCLM (A := A))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
    intro g
    change ‖F (g.comp i)‖ ≤ ‖F‖ * ‖g‖
    apply (F.le_opNorm (g.comp i)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg F)
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
    intro a
    change ‖g (Unitization.inr a)‖ ≤ ‖g‖ * ‖a‖
    simpa only [Unitization.norm_inr] using g.le_opNorm (Unitization.inr a)
  · apply F.opNorm_le_bound (norm_nonneg (unitizationBidual F))
    intro f
    obtain ⟨g, hg, hgnorm⟩ := exists_extension_unitization_norm_eq f
    have hrestrict : g.comp i = f := by
      ext a
      exact hg a
    calc
      ‖F f‖ = ‖unitizationBidual F g‖ := by
        change ‖F f‖ = ‖F (g.comp i)‖
        rw [hrestrict]
      _ ≤ ‖unitizationBidual F‖ * ‖g‖ := (unitizationBidual F).le_opNorm g
      _ = ‖unitizationBidual F‖ * ‖f‖ := by rw [hgnorm]

/-- The bidual inclusion, bundled using its proved original-norm isometry. -/
def unitizationBidualIsometry :
    StrongDual ℂ (StrongDual ℂ A) →ₗᵢ[ℂ]
      StrongDual ℂ (StrongDual ℂ (Unitization ℂ A)) where
  toLinearMap := (unitizationBidual (A := A)).toLinearMap
  norm_map' := norm_unitizationBidual

/-- The unitization embedding preserves the previously constructed product. -/
theorem unitizationBidual_arensProduct (F G : StrongDual ℂ (StrongDual ℂ A)) :
    unitizationBidual (arensProduct F G) =
      arensProduct (unitizationBidual F) (unitizationBidual G) := by
  exact bidualMap_arensProduct
    (inclusionCLM (A := A))
    (fun a b => map_mul (Unitization.inrNonUnitalStarAlgHom ℂ A) a b) F G

/-- The unitization embedding preserves the previously constructed involution. -/
theorem unitizationBidual_bidualStar (F : StrongDual ℂ (StrongDual ℂ A)) :
    unitizationBidual (bidualStar F) = bidualStar (unitizationBidual F) := by
  exact bidualMap_bidualStar
    (inclusionCLM (A := A))
    (fun a => map_star (Unitization.inrNonUnitalStarAlgHom ℂ A) a) F

/-- Compatibility with the original canonical evaluation embedding. -/
@[simp]
theorem unitizationBidual_canonical (a : A) :
    unitizationBidual (NormedSpace.inclusionInDoubleDual ℂ A a) =
      NormedSpace.inclusionInDoubleDual ℂ (Unitization ℂ A) (Unitization.inr a) :=
  bidualMap_canonical
    (inclusionCLM (A := A)) a

/-- The same bidual inclusion is a topological embedding for the prescribed
weak-star topologies. A continuous linear left inverse comes from the second
coordinate of the unitization; this projection is not claimed multiplicative. -/
theorem isEmbedding_unitizationBidual :
    IsEmbedding (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (unitizationBidual (WeakDual.toStrongDual F))) := by
  let i : A →L[ℂ] Unitization ℂ A :=
    (inclusionCLM (A := A))
  let p : Unitization ℂ A →L[ℂ] A :=
    { toLinearMap := Unitization.sndHom ℂ ℂ A
      cont := Unitization.continuous_snd }
  have hleft : Function.LeftInverse (weakStarMap p) (weakStarMap i) := by
    intro F
    apply WeakDual.toStrongDual.injective
    ext f
    change weakStarMap p (weakStarMap i F) f = F f
    rw [weakStarMap_apply, weakStarMap_apply]
    have hcomp : (f.comp p).comp i = f := by
      ext a
      rfl
    rw [hcomp]
  have heq : (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (unitizationBidual (WeakDual.toStrongDual F))) =
      weakStarMap i := by
    funext F
    apply WeakDual.toStrongDual.injective
    ext g
    change F (g.comp i) = weakStarMap i F g
    exact (weakStarMap_apply i F g).symm
  rw [heq]
  exact hleft.isEmbedding (weakStarMap p).continuous (weakStarMap i).continuous

/-- Antimultiplicativity on the original non-unital bidual, obtained using
an injective map rather than by changing its multiplication. -/
theorem bidualStar_arensProduct (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (arensProduct F G) = arensProduct (bidualStar G) (bidualStar F) := by
  apply (unitizationBidualIsometry (A := A)).injective
  change unitizationBidual (bidualStar (arensProduct F G)) =
    unitizationBidual (arensProduct (bidualStar G) (bidualStar F))
  simp only [unitizationBidual_bidualStar, unitizationBidual_arensProduct]
  exact MathlibAnnex.RepresentedBidual.bidualStar_arensProduct _ _

/-- The exact C*-identity for the original operator norm, with no unitality
or nontriviality hypothesis on the source algebra. -/
theorem norm_arensStar_square (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct (bidualStar F) F‖ = ‖F‖ * ‖F‖ := by
  rw [← norm_unitizationBidual (arensProduct (bidualStar F) F),
    unitizationBidual_arensProduct, unitizationBidual_bidualStar,
    MathlibAnnex.RepresentedBidual.norm_arensStar_square, norm_unitizationBidual]

end MathlibAnnex.Analysis.CStarAlgebra.Bidual
