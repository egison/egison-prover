import DesignExamples.TwoCancellationsCommon

namespace DesignExamples.TwoCancellations

open ListCuts

variable {G : Type*} [Group G] [DecidableEq G]

theorem all_results_good {w r : List G} (hr : r ∈ plain w) : Good w r := by
  obtain ⟨c₁, hc₁, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hr
  simp only [List.mem_filter, decide_eq_true_eq] at hc₁ hc₂
  exact pair_sound c₁ c₂ ⟨cuts_sound hc₁.1, hc₁.2⟩ ⟨cuts_sound hc₂.1, hc₂.2⟩

theorem all_results_good_automated {w r : List G} (hr : r ∈ plain w) : Good w r := by
  simp only [plain, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, mem_cuts_iff] at hr
  aesop (add safe pair_sound)

-- 同じパターン関係の正しさが既に共有されている場合の、短い比較対象。
theorem all_results_good_via_matches {w r : List G} (hr : r ∈ plain w) : Good w r := by
  obtain ⟨pre, g, mid, k, post, rfl, rfl⟩ := mem_plain_iff.mp hr
  exact two_cancel_identity pre g mid k post

theorem all_results_good_via_matches_automated {w r : List G} (hr : r ∈ plain w) :
    Good w r := by
  aesop (add simp [mem_plain_iff, Matches]) (add safe two_cancel_identity)

theorem all_many_results_good {n : Nat} {w r : List G} (hr : r ∈ plainMany n w) :
    GoodMany n w r := by
  induction n generalizing w r with
  | zero =>
    have heq : r = w := by simpa [plainMany] using hr
    subst r
    exact ⟨rfl, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    simp only [List.mem_filter, decide_eq_true_eq] at hc
    exact extend_good c ⟨cuts_sound hc.1, hc.2⟩ (ih hs)

theorem all_many_results_good_automated {n : Nat} {w r : List G} (hr : r ∈ plainMany n w) :
    GoodMany n w r := by
  induction n generalizing w r with
  | zero => simp_all [plainMany, GoodMany]
  | succ n ih =>
    simp only [plainMany, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq, mem_cuts_iff] at hr
    aesop (add safe extend_good)

end DesignExamples.TwoCancellations
