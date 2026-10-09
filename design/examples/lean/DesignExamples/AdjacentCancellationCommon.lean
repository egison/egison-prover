import DesignExamples.TwoBlocks

namespace DesignExamples.AdjacentCancellation

variable {A : Type*}

/-- Delete two equal adjacent elements at a selected occurrence. -/
def Step (w u : List A) : Prop :=
  ∃ pre a post, w = pre ++ a :: a :: post ∧ u = pre ++ post

/-- Both results reach a common word in at most one more step each. -/
def Join (u v : List A) : Prop := Relation.Join (Relation.ReflGen Step) u v

/-- Relations of the five tuple patterns, including all their selected values. -/
def CutPatterns (p : List A) (a : A) (s q : List A) (b : A) (t : List A) : Prop :=
  (∃ pre x post, p = pre ∧ a = x ∧ s = post ∧ q = pre ∧ b = x ∧ t = post) ∨
  (∃ pre x post, p = pre ∧ a = x ∧ s = x :: post ∧
    q = pre ++ [x] ∧ b = x ∧ t = post) ∨
  (∃ pre x post, p = pre ++ [x] ∧ a = x ∧ s = post ∧
    q = pre ∧ b = x ∧ t = x :: post) ∨
  (∃ pre x mid y post, p = pre ∧ a = x ∧ s = mid ++ y :: y :: post ∧
    q = pre ++ [x, x] ++ mid ∧ b = y ∧ t = post) ∨
  (∃ pre y mid x post, p = pre ++ [y, y] ++ mid ∧ a = x ∧ s = post ∧
    q = pre ∧ b = y ∧ t = mid ++ x :: x :: post)

/-- Instantiate the generic interval classification and arrange tuple witnesses. -/
theorem cut_patterns (p : List A) (a : A) (s q : List A) (b : A) (t : List A)
    (h : p ++ a :: a :: s = q ++ b :: b :: t) : CutPatterns p a s q b t := by
  rcases TwoBlocks.exhaustive p a a s q b b t h with
    ⟨hp, hab, _, hs⟩ | ⟨hq, hab, hs⟩ | ⟨hp, hab, ht⟩ |
    ⟨mid, hq, hs⟩ | ⟨mid, hp, ht⟩
  · exact Or.inl ⟨p, a, s, rfl, rfl, rfl, hp.symm, hab.symm, hs.symm⟩
  · subst b
    exact Or.inr (Or.inl ⟨p, a, t, rfl, rfl, hs, hq, rfl, rfl⟩)
  · subst a
    exact Or.inr (Or.inr (Or.inl ⟨q, b, s, hp, rfl, rfl, rfl, rfl, ht⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, a, mid, b, t, rfl, rfl, hs, hq, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨q, b, mid, a, s, hp, rfl, rfl, rfl, rfl, ht⟩)))

/-- Deleting the other, disjoint pair closes both branches. -/
theorem join_disjoint (pre : List A) (a : A) (mid : List A) (b : A) (post : List A) :
    Join (pre ++ (mid ++ b :: b :: post)) (pre ++ a :: a :: (mid ++ post)) := by
  refine ⟨pre ++ (mid ++ post), Relation.ReflGen.single ?_, Relation.ReflGen.single ?_⟩
  · exact ⟨pre ++ mid, b, post, by simp [List.append_assoc], by simp [List.append_assoc]⟩
  · exact ⟨pre, a, mid ++ post, rfl, rfl⟩

theorem join_symm {u v : List A} (h : Join u v) : Join v u := by
  obtain ⟨z, hu, hv⟩ := h
  exact ⟨z, hv, hu⟩

theorem join_self (w : List A) : Join w w := ⟨w, .refl, .refl⟩

/-- Each step removes exactly two elements. -/
theorem step_length {w u : List A} (h : Step w u) : u.length + 2 = w.length := by
  obtain ⟨pre, a, post, rfl, rfl⟩ := h
  simp only [List.length_append, List.length_cons]
  omega

end DesignExamples.AdjacentCancellation
