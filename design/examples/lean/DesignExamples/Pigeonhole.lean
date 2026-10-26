import DesignExamples.Common

namespace DesignExamples.Pigeonhole

def Same3 {n : Nat} (f : Fin n → Color) : Prop :=
  ∃ i c j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    f i = c ∧ f j = c ∧ f k = c

def Split3 (f : Fin 3 → Color) : Prop :=
  ∃ i c j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    f i = c ∧ f j = c ∧ f k = c.opposite

def firstIndex (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩
def lastIndex (i : Fin 2) : Fin 5 := ⟨3 + i.val, by omega⟩

theorem firstIndex_injective : Function.Injective firstIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

theorem lastIndex_injective : Function.Injective lastIndex := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lastIndex] at hv
  omega

theorem firstIndex_ne_lastIndex (i : Fin 3) (j : Fin 2) :
    firstIndex i ≠ lastIndex j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [firstIndex, lastIndex] at hv
  omega

theorem three_color_cases (f : Fin 3 → Color) : Same3 f ∨ Split3 f := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2
  · exact Or.inl ⟨0, .red, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩
  · exact Or.inr ⟨0, .red, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩
  · exact Or.inr ⟨0, .red, 2, 1, by decide, by decide, by decide, h0, h2, h1⟩
  · exact Or.inr ⟨1, .blue, 2, 0, by decide, by decide, by decide, h1, h2, h0⟩
  · exact Or.inr ⟨1, .red, 2, 0, by decide, by decide, by decide, h1, h2, h0⟩
  · exact Or.inr ⟨0, .blue, 2, 1, by decide, by decide, by decide, h0, h2, h1⟩
  · exact Or.inr ⟨0, .blue, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩
  · exact Or.inl ⟨0, .blue, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩

theorem two_color_cases (f : Fin 2 → Color) (c : Color) :
    (∃ i, f i = c) ∨
    (∃ i j, i ≠ j ∧ f i = c.opposite ∧ f j = c.opposite) := by
  by_cases h0 : f 0 = c
  · exact Or.inl ⟨0, h0⟩
  by_cases h1 : f 1 = c
  · exact Or.inl ⟨1, h1⟩
  exact Or.inr ⟨0, 1, by decide,
    Color.eq_opposite_of_ne h0, Color.eq_opposite_of_ne h1⟩

theorem five_colors (f : Fin 5 → Color) : Same3 f := by
  let first : Fin 3 → Color := fun i => f (firstIndex i)
  let last : Fin 2 → Color := fun i => f (lastIndex i)
  rcases three_color_cases first with h | h
  · obtain ⟨i, c, j, k, hij, hik, hjk, hi, hj, hk⟩ := h
    exact ⟨firstIndex i, c, firstIndex j, firstIndex k,
      fun e => hij (firstIndex_injective e),
      fun e => hik (firstIndex_injective e),
      fun e => hjk (firstIndex_injective e), hi, hj, hk⟩
  · obtain ⟨i, c, j, k, hij, hik, hjk, hi, hj, hk⟩ := h
    rcases two_color_cases last c with ⟨l, hl⟩ | ⟨l, m, hlm, hl, hm⟩
    · exact ⟨firstIndex i, c, firstIndex j, lastIndex l,
        fun e => hij (firstIndex_injective e),
        firstIndex_ne_lastIndex i l, firstIndex_ne_lastIndex j l,
        hi, hj, hl⟩
    · exact ⟨firstIndex k, c.opposite, lastIndex l, lastIndex m,
        firstIndex_ne_lastIndex k l, firstIndex_ne_lastIndex k m,
        fun e => hlm (lastIndex_injective e), hk, hl, hm⟩

end DesignExamples.Pigeonhole
