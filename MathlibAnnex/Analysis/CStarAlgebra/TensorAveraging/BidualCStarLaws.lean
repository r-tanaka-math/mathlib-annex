import MathlibAnnex.Analysis.CStarAlgebra.TensorAveraging.RepresentedBidualSeparation

/-!
# The C*-laws for the explicitly defined first-Arens product

All operations are still explicit functions on the fixed Banach bidual.  The
coefficient family proves the missing antimultiplicativity and the exact C* norm
law. Separate weak-star continuity in the second variable then follows from the
involution and the already known continuity in the first variable. No arbitrary
bilinear Arens regularity theorem is used. Zero algebras are handled explicitly.
C03 proof-source candidate, unbuilt.
-/
set_option autoImplicit false
noncomputable section
open Topology

namespace MathlibAnnex.RepresentedBidual
universe u
variable {A : Type u} [CStarAlgebra A]

/-- The zero-algebra branch does not request a normalized state. -/
theorem raw_eq_zero_of_subsingleton [Subsingleton A]
    (F : StrongDual ℂ (StrongDual ℂ A)) : F = 0 := by
  have hf : ∀ f : StrongDual ℂ A, f = 0 := by
    intro f
    ext a
    rw [Subsingleton.elim a 0, map_zero]
    rfl
  ext f
  rw [hf f, map_zero]
  rfl

@[simp] theorem arensProduct_zero_left (G : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct 0 G = 0 := by ext f; rfl

@[simp] theorem arensProduct_zero_right (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct F 0 = 0 := by
  ext f
  change F (rightSlice 0 f) = 0
  have h : rightSlice (0 : StrongDual ℂ (StrongDual ℂ A)) f = 0 := by ext a; rfl
  rw [h, map_zero]

@[simp] theorem arensProduct_add_left (F G K : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (F + G) K = arensProduct F K + arensProduct G K := by ext f; rfl

@[simp] theorem arensProduct_smul_left (c : ℂ) (F G : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (c • F) G = c • arensProduct F G := by ext f; rfl

@[simp] theorem arensProduct_add_right (F G K : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct F (G + K) = arensProduct F G + arensProduct F K := by
  ext f
  have h : rightSlice (G + K) f = rightSlice G f + rightSlice K f := by ext a; rfl
  change F (rightSlice (G + K) f) = F (rightSlice G f) + F (rightSlice K f)
  rw [h, map_add]

@[simp] theorem arensProduct_smul_right (c : ℂ) (F G : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct F (c • G) = c • arensProduct F G := by
  ext f
  have h : rightSlice (c • G) f = c • rightSlice G f := by ext a; rfl
  change F (rightSlice (c • G) f) = c • F (rightSlice G f)
  rw [h, map_smul]

@[simp] theorem arensProduct_one_left (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct (NormedSpace.inclusionInDoubleDual ℂ A 1) F = F := by
  ext f
  change F (multiplicationForm f 1) = F f
  congr 1
  ext a
  simp only [multiplicationForm_apply, one_mul]

@[simp] theorem arensProduct_one_right (F : StrongDual ℂ (StrongDual ℂ A)) :
    arensProduct F (NormedSpace.inclusionInDoubleDual ℂ A 1) = F := by
  ext f
  change F (rightSlice (NormedSpace.inclusionInDoubleDual ℂ A 1) f) = F f
  congr 1
  ext a
  change f (a * 1) = f a
  rw [mul_one]

/-- Antimultiplicativity is forced by the separating represented family. -/
theorem bidualStar_arensProduct (F G : StrongDual ℂ (StrongDual ℂ A)) :
    bidualStar (arensProduct F G) = arensProduct (bidualStar G) (bidualStar F) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · letI := hA
    rw [raw_eq_zero_of_subsingleton (bidualStar (arensProduct F G)),
      raw_eq_zero_of_subsingleton (arensProduct (bidualStar G) (bidualStar F))]
  · letI := hA
    apply FunctionalFamily.ext
    intro f
    simp only [FunctionalFamily.image_star, FunctionalFamily.image_product, star_mul]

/-- Exact original-bidual C* norm identity, including the trivial algebra. -/
theorem norm_arensStar_square (F : StrongDual ℂ (StrongDual ℂ A)) :
    ‖arensProduct (bidualStar F) F‖ = ‖F‖ * ‖F‖ := by
  apply le_antisymm
  · simpa only [norm_bidualStar] using norm_arensProduct_le (bidualStar F) F
  · rcases subsingleton_or_nontrivial A with hA | hA
    · letI := hA
      rw [raw_eq_zero_of_subsingleton F]
      simp only [ContinuousLinearMap.opNorm_zero, zero_mul]
      positivity
    · letI := hA
      exact FunctionalFamily.norm_square_le F

/-- The canonical involution is genuinely weak-star continuous. -/
theorem bidualStar_weakStarContinuous :
    Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (bidualStar (WeakDual.toStrongDual F))) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun F : WeakDual ℂ (StrongDual ℂ A) => star (F (dualStar f)))
  exact (WeakDual.eval_continuous (dualStar f)).star

/-- Multiplication in the second variable is continuous, derived rather
than assumed. The two stars reverse the order twice. -/
theorem continuous_arensProduct_right (F : StrongDual ℂ (StrongDual ℂ A)) :
    Continuous (fun G : WeakDual ℂ (StrongDual ℂ A) =>
      StrongDual.toWeakDual (arensProduct F (WeakDual.toStrongDual G))) := by
  have h := bidualStar_weakStarContinuous.comp
    ((continuous_arensProduct_left (bidualStar F)).comp bidualStar_weakStarContinuous)
  convert h using 1
  funext G
  change StrongDual.toWeakDual (arensProduct F (WeakDual.toStrongDual G)) =
    StrongDual.toWeakDual (bidualStar
      (arensProduct (bidualStar (WeakDual.toStrongDual G)) (bidualStar F)))
  rw [bidualStar_arensProduct, bidualStar_bidualStar, bidualStar_bidualStar]

end MathlibAnnex.RepresentedBidual
