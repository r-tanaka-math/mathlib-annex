import MathlibAnnex

open Metric Set
open MathlibAnnex.IsometryEquiv

-- Downstream use needs only the public root import.
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {t : Set F} (f : s ≃ᵢ t)
    (hs : IsOpen s) (hsc : IsConnected s) (ht : IsOpen t) :
    ∃! A : E ≃ᵃⁱ[ℝ] F, ∀ x : s, A (x : E) = ((f x : t) : F) :=
  existsUnique_affineExtension f hs hsc ht

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E) : ∃! A : E ≃ᵃⁱ[ℝ] E,
      ∀ x : ball c (1 : ℝ), A (x : E) = (x : E) :=
  existsUnique_affineExtension_ball (IsometryEquiv.refl _) (by norm_num) (by norm_num)
