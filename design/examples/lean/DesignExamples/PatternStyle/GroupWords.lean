-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.GroupWords

variable {G : Type*} [Group G]

def Reduced (w : List G) : Prop :=
  ¬∃ pre g post, w = pre ++ g :: g⁻¹ :: post

theorem cancel_pair (pre : List G) (g : G) (post : List G) :
    (pre ++ g :: g⁻¹ :: post).prod = (pre ++ post).prod := by
  simp [List.prod_append]

theorem exists_reduced (w : List G) :
    ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length := by
  classical
  suffices h : ∀ n, ∀ w : List G, w.length = n →
      ∃ r, Reduced r ∧ r.prod = w.prod ∧ r.length ≤ w.length from h w.length w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn
    rcases Classical.em (¬(∃ pre g post, w = pre ++ g :: g⁻¹ :: post)) with heq | hn
    ·
      exact ⟨w, heq, rfl, le_rfl⟩
    · obtain ⟨pre, g, post, heq⟩ := not_not.mp hn
      subst w
      have hlt : (pre ++ post).length < n := by simp_all; omega
      obtain ⟨r, hred, hprod, hlen⟩ := ih _ hlt (pre ++ post) rfl
      refine ⟨r, hred, hprod.trans (cancel_pair pre g post).symm, ?_⟩
      simp only [List.length_append, List.length_cons] at *
      omega

end DesignExamples.PatternStyle.GroupWords
