import DesignExamples.Alternating.Reductions
import DesignExamples.Alternating.Patterns

/-!
Manual elaboration of the proposed observation-pattern proof.
Pattern relations are converted to the same conditions used by ordinary Lean.
No automatic translation from the accompanying `.pmop` file is claimed.
-/

namespace DesignExamples.Alternating.PatternStyle

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem contains_three (h5 : 5 ≤ Nat.card α) {N : Subgroup (Perm α)}
    (hle : N ≤ alternatingGroup α) (hN : NormalInAlternating N)
    (σ : Perm α) (hσ : σ ∈ N) (hne : σ ≠ 1) : ∃ τ ∈ N, τ.IsThreeCycle := by
  rcases matching_cases_exhaustive σ (hle hσ) hne with
    ⟨a, b, c, h⟩ | ⟨a, b, c, d, h⟩ |
    ⟨a, b, c, d, e, h⟩ | ⟨a, b, c, d, h⟩
  · obtain ⟨hn, heq⟩ := (onlyThreeMatch_iff σ a b c).mp h
    exact ⟨σ, hσ, heq ▸ cycle3_isThreeCycle hn⟩
  · exact three_of_path4 hN hσ ((path4Match_iff σ a b c d).mp h)
  · exact three_of_three_extra hN hσ ((threeExtraMatch_iff σ a b c d e).mp h)
  · exact three_of_two_pairs h5 hN hσ ((twoPairsMatch_iff σ a b c d).mp h)

theorem alternating_simple (h5 : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) :=
  simple_of_three_cycle_production h5 (fun _ hle hN σ hσ hne =>
    contains_three h5 hle hN σ hσ hne)

theorem a5_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternating_simple (by simp)

end DesignExamples.Alternating.PatternStyle
