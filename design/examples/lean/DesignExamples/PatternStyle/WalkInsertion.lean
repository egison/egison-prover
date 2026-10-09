-- 二つのリストを同時に照合するパターンの関係と各腕を、手動で展開した版。
import DesignExamples.WalkInsertion

namespace DesignExamples.PatternStyle.WalkInsertion

open DesignExamples.WalkInsertion DesignExamples.WalkPaths

variable {A : Type*}

theorem insert_closed_walk (E : A → A → Prop) (s t v : A) (w loop : List A)
    (hw : Walk E s t w) (hc : Walk E v v loop) (hv : v ∈ w) :
    ∃ r, Inserted v w loop r ∧ Walk E s t r ∧ r.length + 1 = w.length + loop.length := by
  rcases insertion_cases E hv hc with ⟨pre, post, hweq, hloop⟩ | ⟨pre, post, mid, hweq, hloop⟩
  · subst w loop
    refine ⟨pre ++ v :: post, ⟨pre, post, rfl, Or.inl ⟨rfl, rfl⟩⟩, hw, ?_⟩
    simp
  · subst w loop
    exact ⟨pre ++ v :: (mid ++ v :: post),
      ⟨pre, post, rfl, Or.inr ⟨mid, rfl, rfl⟩⟩,
      insert_walk E s t pre v mid post hw hc, insert_length pre v mid post⟩

end DesignExamples.PatternStyle.WalkInsertion
