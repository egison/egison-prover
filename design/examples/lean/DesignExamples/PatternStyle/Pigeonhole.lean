-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.Pigeonhole

theorem collision {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (h : Fintype.card B < Fintype.card A) :
    ∃ x v y, x ≠ y ∧ f x = v ∧ f y = v := by
  obtain ⟨x, y, hxy, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
  exact ⟨x, f x, y, hxy, rfl, heq.symm⟩

theorem list_collision {A : Type*} [Fintype A] (w : List A)
    (h : Fintype.card A < w.length) :
    ∃ pre x mid post, w = pre ++ x :: (mid ++ x :: post) := by
  apply repeated_split
  intro hn
  have hb := hn.length_le_card
  omega

end DesignExamples.PatternStyle.Pigeonhole
