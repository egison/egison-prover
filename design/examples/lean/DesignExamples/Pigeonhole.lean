import DesignExamples.Common

namespace DesignExamples.Pigeonhole

theorem collision {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (h : Fintype.card B < Fintype.card A) :
    ∃ x y, x ≠ y ∧ f x = f y :=
  Fintype.exists_ne_map_eq_of_card_lt f h

theorem list_collision {A : Type*} [Fintype A] (w : List A)
    (h : Fintype.card A < w.length) :
    ∃ pre x mid post, w = pre ++ x :: (mid ++ x :: post) := by
  apply repeated_split
  intro hn
  have hb := hn.length_le_card
  omega

end DesignExamples.Pigeonhole
