-- 提案する matchAll の意味を、証拠を持つ有限列挙の組合せで記述した Lean 版。
-- 提案ソースから自動生成する変換器ではない。
import DesignExamples.TwoCancellations

namespace DesignExamples.PatternStyle.TwoCancellations

open DesignExamples.ListCuts DesignExamples.CertifiedList
open DesignExamples.TwoCancellations

variable {G : Type*} [Group G] [DecidableEq G]

def inverseCuts (w : List G) := keep (certifiedCuts w) InversePair

theorem values_inverseCuts (w : List G) :
    values (inverseCuts w) = (cuts w).filter (fun c => decide (InversePair c)) := by
  rw [inverseCuts, values_keep, values_certifiedCuts]

def certified (w : List G) : Certified (Good w) :=
  bind (inverseCuts w) fun c₁ h₁ =>
    mapWithProof (inverseCuts c₁.post) (removeTwo c₁) fun c₂ h₂ => pair_sound c₁ c₂ h₁ h₂

theorem values_certified (w : List G) : values (certified w) = plain w := by
  unfold certified
  rw [values_bind _ _ (fun c₁ =>
    ((cuts c₁.post).filter fun c => decide (InversePair c)).map (removeTwo c₁))
      (fun c₁ _ => by rw [values_map, values_inverseCuts])]
  rw [values_inverseCuts]
  rfl

theorem all_certified_results_good {w r : List G} (hr : r ∈ values (certified w)) :
    Good w r := sound (certified w) hr

-- 普通の List に証明を戻したときも、対象と結論は通常の版と同じである。
theorem all_results_good {w r : List G} (hr : r ∈ plain w) : Good w r := by
  exact sound (certified w) (by simpa only [values_certified] using hr)

theorem mem_certified_iff {w r : List G} : r ∈ values (certified w) ↔ Matches w r := by
  rw [values_certified, mem_plain_iff]

-- 再帰呼出しの結果の型に、後半についての帰納仮定が含まれる。
def certifiedMany : (n : Nat) → (w : List G) → Certified (GoodMany n w)
  | 0, w => [⟨w, rfl, by simp⟩]
  | n + 1, w =>
    bind (inverseCuts w) fun c hc =>
      mapWithProof (certifiedMany n c.post) (fun r => c.pre ++ r) fun r hr => extend_good c hc hr

theorem values_certifiedMany (n : Nat) (w : List G) :
    values (certifiedMany n w) = plainMany n w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    simp only [certifiedMany, plainMany]
    rw [values_bind _ _ (fun c => (plainMany n c.post).map fun r => c.pre ++ r)
      (fun c _ => by rw [values_map, ih])]
    rw [values_inverseCuts]

theorem all_many_results_good {n : Nat} {w r : List G} (hr : r ∈ plainMany n w) :
    GoodMany n w r := by
  exact sound (certifiedMany n w) (by simpa only [values_certifiedMany] using hr)

theorem mem_certifiedMany_iff {n : Nat} {w r : List G} :
    r ∈ values (certifiedMany n w) ↔ MatchesMany n w r := by
  rw [values_certifiedMany, mem_plainMany_iff]

end DesignExamples.PatternStyle.TwoCancellations
