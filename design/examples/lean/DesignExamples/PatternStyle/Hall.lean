-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.Hall

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def neighbors (E : X → Y → Prop) [DecidableRel E] (S : Finset X) : Finset Y :=
  S.biUnion (fun x => Finset.univ.filter (E x))

def HallCondition (E : X → Y → Prop) [DecidableRel E] : Prop :=
  ∀ S : Finset X, S.card ≤ (neighbors E S).card

def Closed (E : X → Y → Prop) [DecidableRel E] (S : Finset X) (T : Finset Y) : Prop :=
  neighbors E S ⊆ T

def Matching (E : X → Y → Prop) (f : X → Y) : Prop :=
  Function.Injective f ∧ ∀ x, E x (f x)

instance (E : X → Y → Prop) [DecidableRel E] (S : Finset X) (T : Finset Y) :
    Decidable (Closed E S T) := inferInstanceAs (Decidable (neighbors E S ⊆ T))

instance (E : X → Y → Prop) [DecidableRel E] (f : X → Y) :
    Decidable (Matching E f) :=
  inferInstanceAs (Decidable (Function.Injective f ∧ ∀ x, E x (f x)))

def badPairs (E : X → Y → Prop) [DecidableRel E] : Finset (Finset X × Finset Y) :=
  (Finset.univ.powerset ×ˢ Finset.univ.powerset).filter
    (fun p => Closed E p.1 p.2 ∧ p.2.card < p.1.card)

omit [DecidableEq X] in
theorem mem_badPairs (E : X → Y → Prop) [DecidableRel E]
    (S : Finset X) (T : Finset Y) :
    (S, T) ∈ badPairs E ↔ Closed E S T ∧ T.card < S.card := by
  simp [badPairs]

omit [Fintype X] [DecidableEq X] in
theorem hall_iff_no_bad_pair (E : X → Y → Prop) [DecidableRel E] :
    HallCondition E ↔ ¬∃ S T, Closed E S T ∧ T.card < S.card := by
  constructor
  · intro h ⟨S, T, hclosed, hsmall⟩
    have hle := (h S).trans (Finset.card_le_card hclosed)
    omega
  · intro h S
    by_contra hn
    exact h ⟨S, neighbors E S, Finset.Subset.refl _, by omega⟩

omit [DecidableEq X] in
theorem hall_from_card (E : X → Y → Prop) [DecidableRel E] (h : HallCondition E) :
    ∃ f, Matching E f := by
  obtain ⟨f, hfinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun x => Finset.univ.filter (E x))).mp h
  exact ⟨f, hfinj, fun x => (Finset.mem_filter.mp (hf x)).2⟩

def matchings (E : X → Y → Prop) [DecidableRel E] : Finset (X → Y) :=
  Finset.univ.filter (Matching E)

omit [Fintype X] [DecidableEq X] in
theorem matching_implies_hall (E : X → Y → Prop) [DecidableRel E]
    (f : X → Y) (hf : Matching E f) : HallCondition E := by
  intro S
  have hsub : S.image f ⊆ neighbors E S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨by simp, hf.2 x⟩⟩
  simpa [Finset.card_image_of_injective _ hf.1] using Finset.card_le_card hsub

omit [DecidableEq X] in
theorem hall_iff_matching (E : X → Y → Prop) [DecidableRel E] :
    HallCondition E ↔ ∃ f, Matching E f :=
  ⟨hall_from_card E, fun ⟨f, hf⟩ => matching_implies_hall E f hf⟩

theorem mem_matchings (E : X → Y → Prop) [DecidableRel E] (f : X → Y) :
    f ∈ matchings E ↔ Matching E f := by
  simp [matchings]

theorem pattern_hall (E : X → Y → Prop) [DecidableRel E]
    (h : badPairs E = ∅) : (matchings E).Nonempty := by
  have hn : ¬∃ S T, Closed E S T ∧ T.card < S.card := by
    rintro ⟨S, T, hp⟩
    have hm := (mem_badPairs E S T).mpr hp
    simp [h] at hm
  obtain ⟨f, hf⟩ := hall_from_card E ((hall_iff_no_bad_pair E).mpr hn)
  exact ⟨f, (mem_matchings E f).mpr hf⟩

omit [DecidableEq X] in
theorem hall (E : X → Y → Prop) [DecidableRel E]
    (h : ¬∃ S T, Closed E S T ∧ T.card < S.card) : ∃ f, Matching E f := by
  have hc : HallCondition E := (hall_iff_no_bad_pair E).mpr h
  obtain ⟨f, hf⟩ := hall_from_card E hc
  exact ⟨f, hf⟩

end DesignExamples.PatternStyle.Hall
