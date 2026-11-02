import DesignExamples.Alternating.Coverage

/-!
Relations for finite-function observation patterns. Selecting an entry consumes
its input key, so the selected keys are distinct. Unselected entries are unrestricted.
The equality pattern in `OnlyThreeMatch` applies to the original permutation.
These definitions specify the proposed patterns; they are not a syntax elaborator.
-/

namespace DesignExamples.Alternating

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

def Observes (σ : Perm α) (entries : List (α × α)) : Prop :=
  (entries.map Prod.fst).Nodup ∧ ∀ p ∈ entries, σ p.1 = p.2

def OnlyThreeMatch (σ : Perm α) (a b c : α) : Prop :=
  Observes σ [(a, b), (b, c), (c, a)] ∧ σ = cycle3 a b c

def Path4Match (σ : Perm α) (a b c d : α) : Prop :=
  Observes σ [(a, b), (b, c), (c, d), (d, σ d)]

def ThreeExtraMatch (σ : Perm α) (a b c d e : α) : Prop :=
  Observes σ [(a, b), (b, c), (c, a), (d, e), (e, σ e)]

def TwoPairsMatch (σ : Perm α) (a b c d : α) : Prop :=
  Observes σ [(a, b), (b, a), (c, d), (d, c)]

omit [Fintype α] in
theorem onlyThreeMatch_iff (σ : Perm α) (a b c : α) :
    OnlyThreeMatch σ a b c ↔ [a, b, c].Nodup ∧ σ = cycle3 a b c := by
  constructor
  · rintro ⟨h, heq⟩
    exact ⟨by simpa using h.1, heq⟩
  · rintro ⟨hn, rfl⟩
    refine ⟨⟨by simpa using hn, ?_⟩, rfl⟩
    simp_all [cycle3, swap_apply_def, List.nodup_cons]
    grind

omit [Fintype α] [DecidableEq α] in
theorem path4Match_iff (σ : Perm α) (a b c d : α) :
    Path4Match σ a b c d ↔ Path4 σ a b c d := by
  simp [Path4Match, Observes, Path4]

omit [Fintype α] [DecidableEq α] in
theorem threeExtraMatch_iff (σ : Perm α) (a b c d e : α) :
    ThreeExtraMatch σ a b c d e ↔ ThreeExtra σ a b c d e := by
  simp [ThreeExtraMatch, Observes, ThreeExtra]

omit [Fintype α] [DecidableEq α] in
theorem twoPairsMatch_iff (σ : Perm α) (a b c d : α) :
    TwoPairsMatch σ a b c d ↔ TwoPairs σ a b c d := by
  simp [TwoPairsMatch, Observes, TwoPairs]

def MatchingCases (σ : Perm α) : Prop :=
  (∃ a b c, OnlyThreeMatch σ a b c) ∨
  (∃ a b c d, Path4Match σ a b c d) ∨
  (∃ a b c d e, ThreeExtraMatch σ a b c d e) ∨
  (∃ a b c d, TwoPairsMatch σ a b c d)

omit [Fintype α] in
theorem matchingCases_iff_cases (σ : Perm α) : MatchingCases σ ↔ Cases σ := by
  simp only [MatchingCases, Cases, onlyThreeMatch_iff, path4Match_iff,
    threeExtraMatch_iff, twoPairsMatch_iff]

theorem matching_cases_exhaustive (σ : Perm α) (hσ : σ ∈ alternatingGroup α)
    (hne : σ ≠ 1) : MatchingCases σ :=
  (matchingCases_iff_cases σ).mpr (cases_exhaustive σ hσ hne)

end DesignExamples.Alternating
