import DesignExamples.Alternating.Reductions

/-!
Ordinary Lean proof, using exactly the coverage and commutator lemmas supplied
to the pattern-oriented proposal and its manual elaboration.
-/

namespace DesignExamples.Alternating.Ordinary

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem contains_three (h5 : 5 ≤ Nat.card α) {N : Subgroup (Perm α)}
    (hle : N ≤ alternatingGroup α) (hN : NormalInAlternating N)
    (σ : Perm α) (hσ : σ ∈ N) (hne : σ ≠ 1) : ∃ τ ∈ N, τ.IsThreeCycle := by
  rcases cases_exhaustive σ (hle hσ) hne with
    ⟨a, b, c, hn, heq⟩ | ⟨a, b, c, d, h⟩ |
    ⟨a, b, c, d, e, h⟩ | ⟨a, b, c, d, h⟩
  · exact ⟨σ, hσ, heq ▸ cycle3_isThreeCycle hn⟩
  · exact three_of_path4 hN hσ h
  · exact three_of_three_extra hN hσ h
  · exact three_of_two_pairs h5 hN hσ h

/-- The usual statement, unchanged by the use of patterns in the other proof. -/
theorem alternating_simple (h5 : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) :=
  simple_of_three_cycle_production h5 (fun _ hle hN σ hσ hne =>
    contains_three h5 hle hN σ hσ hne)

theorem a5_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternating_simple (by simp)

end DesignExamples.Alternating.Ordinary
