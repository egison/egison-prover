import DesignExamples.WalkInsertionCommon

namespace DesignExamples.WalkInsertion

open DesignExamples.WalkPaths

variable {A : Type*}

theorem insert_closed_walk (E : A → A → Prop) (s t v : A) (w loop : List A)
    (hw : Walk E s t w) (hc : Walk E v v loop) (hv : v ∈ w) :
    ∃ r, Inserted v w loop r ∧ Walk E s t r ∧ r.length + 1 = w.length + loop.length := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hv
  rcases closed_split E hc with rfl | ⟨mid, rfl⟩
  · refine ⟨pre ++ v :: post, ⟨pre, post, rfl, Or.inl ⟨rfl, rfl⟩⟩, hw, ?_⟩
    simp
  · exact ⟨pre ++ v :: (mid ++ v :: post),
      ⟨pre, post, rfl, Or.inr ⟨mid, rfl, rfl⟩⟩,
      insert_walk E s t pre v mid post hw hc, insert_length pre v mid post⟩

end DesignExamples.WalkInsertion
