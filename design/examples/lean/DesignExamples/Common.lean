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

inductive D where
  | one | two | three | four | five
  deriving DecidableEq, Fintype

def D.val : D → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4 | .five => 5

theorem take_one {A : Type*} [DecidableEq A] (S : Finset A) (x : A) (hx : x ∈ S) :
    S.val = x ::ₘ (S.erase x).val := (Multiset.cons_erase hx).symm

theorem take_two {A : Type*} [DecidableEq A] (S : Finset A) (x y : A)
    (hx : x ∈ S) (hy : y ∈ S) (hne : y ≠ x) :
    S.val = x ::ₘ y ::ₘ ((S.erase x).erase y).val := by
  change S.val = x ::ₘ y ::ₘ (S.erase x).val.erase y
  rw [Multiset.cons_erase (Finset.mem_erase.mpr ⟨hne, hy⟩)]
  exact take_one S x hx

theorem repeated_split {A : Type*} (w : List A) (h : ¬w.Nodup) :
    ∃ pre v mid post, w = pre ++ v :: (mid ++ v :: post) := by
  classical
  induction w with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a ∈ l
    · obtain ⟨pre, post, heq⟩ := List.mem_iff_append.mp ha
      exact ⟨[], a, pre, post, by simp [heq]⟩
    · have hn : ¬l.Nodup := fun hl => h (List.nodup_cons.mpr ⟨ha, hl⟩)
      obtain ⟨pre, v, mid, post, heq⟩ := ih hn
      exact ⟨a :: pre, v, mid, post, by simp [heq]⟩

end DesignExamples
