import Mathlib

namespace DesignExamples

inductive Color where
  | red | blue
  deriving DecidableEq, Fintype

def Color.opposite : Color → Color
  | .red => .blue
  | .blue => .red

@[simp] theorem Color.opposite_opposite (c : Color) :
    c.opposite.opposite = c := by
  cases c <;> rfl

theorem Color.eq_opposite_of_ne {a c : Color} (h : a ≠ c) : a = c.opposite := by
  cases a <;> cases c <;> simp_all [Color.opposite]

end DesignExamples
