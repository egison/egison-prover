import DesignExamples.AdjacentCancellationCommon

namespace DesignExamples.AdjacentCancellation

variable {A : Type*}

/-- Compare the five shapes using exactly the coverage available to the pattern source. -/
theorem local_confluence {w u v : List A} (hu : Step w u) (hv : Step w v) : Join u v := by
  obtain ⟨p, a, s, rfl, rfl⟩ := hu
  obtain ⟨q, b, t, hsource, rfl⟩ := hv
  rcases cut_patterns p a s q b t hsource with
    ⟨pre, x, post, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨pre, x, post, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨pre, x, post, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨pre, x, mid, y, post, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨pre, y, mid, x, post, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals try simp only [List.append_assoc, List.cons_append, List.nil_append]
  all_goals first
    | exact join_self _
    | exact join_disjoint _ _ _ _ _
    | apply join_symm; exact join_disjoint _ _ _ _ _

/-- A Lean proof that uses the generic block classification directly. -/
theorem local_confluence_by_intervals {w u v : List A}
    (hu : Step w u) (hv : Step w v) : Join u v := by
  obtain ⟨p, a, s, rfl, rfl⟩ := hu
  obtain ⟨q, b, t, hsource, rfl⟩ := hv
  rcases TwoBlocks.exhaustive p a a s q b b t hsource with
    ⟨rfl, rfl, _, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨mid, rfl, rfl⟩ | ⟨mid, rfl, rfl⟩
  all_goals try simp only [List.append_assoc, List.cons_append, List.nil_append]
  all_goals first
    | exact join_self _
    | exact join_disjoint _ _ _ _ _
    | apply join_symm; exact join_disjoint _ _ _ _ _

/-- The stronger one-step joining property also gives joining after any number of steps. -/
theorem confluence {w u v : List A}
    (hu : Relation.ReflTransGen Step w u) (hv : Relation.ReflTransGen Step w v) :
    Relation.Join (Relation.ReflTransGen Step) u v := by
  apply Relation.church_rosser (fun _ _ _ h₁ h₂ => ?_) hu hv
  obtain ⟨z, h₁z, h₂z⟩ := local_confluence h₁ h₂
  exact ⟨z, h₁z, h₂z.to_reflTransGen⟩

end DesignExamples.AdjacentCancellation
