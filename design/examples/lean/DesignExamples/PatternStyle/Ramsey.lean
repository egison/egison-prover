-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.Ramsey

def Monochromatic {n : Nat} (edge : Sym2 (Fin n) → Color) (x y z : Fin n) : Prop :=
  x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    ∃ c, edge s(x, y) = c ∧ edge s(y, z) = c ∧ edge s(x, z) = c

def neighbors (edge : Sym2 (Fin 6) → Color) (v : Fin 6) (c : Color) : Finset (Fin 6) :=
  (Finset.univ.erase v).filter (fun w => edge s(v, w) = c)

theorem neighbors_total (edge : Sym2 (Fin 6) → Color) (v : Fin 6) :
    (neighbors edge v .red).card + (neighbors edge v .blue).card = 5 := by
  have hpartition : neighbors edge v .red ∪ neighbors edge v .blue = Finset.univ.erase v := by
    ext w
    simp only [neighbors, Finset.mem_union, Finset.mem_filter]
    cases edge s(v, w) <;> simp
  have hdisjoint : Disjoint (neighbors edge v .red) (neighbors edge v .blue) := by
    rw [Finset.disjoint_left]
    intro w hr hb
    have hr' := (Finset.mem_filter.mp hr).2
    have hb' := (Finset.mem_filter.mp hb).2
    rw [hr'] at hb'
    cases hb'
  rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  simp

theorem pigeonhole_edges (edge : Sym2 (Fin 6) → Color) (v : Fin 6) :
    ∃ c, 3 ≤ (neighbors edge v c).card := by
  have ht := neighbors_total edge v
  by_cases hr : 3 ≤ (neighbors edge v .red).card
  · exact ⟨.red, hr⟩
  · exact ⟨.blue, by omega⟩

def Star (edge : Sym2 (Fin 6) → Color) (v x y z : Fin 6) (c : Color) : Prop :=
  v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    edge s(v, x) = c ∧ edge s(v, y) = c ∧ edge s(v, z) = c

theorem pigeonhole_edges_at (edge : Sym2 (Fin 6) → Color) (v : Fin 6) :
    ∃ x c y z, Star edge v x y z c := by
  obtain ⟨c, hc⟩ := pigeonhole_edges edge v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < (neighbors edge v c).card)
  have px := Finset.mem_filter.mp hx
  have py := Finset.mem_filter.mp hy
  have pz := Finset.mem_filter.mp hz
  exact ⟨x, c, y, z, (Finset.mem_erase.mp px.1).1.symm,
    (Finset.mem_erase.mp py.1).1.symm, (Finset.mem_erase.mp pz.1).1.symm,
    hxy, hxz, hyz, px.2, py.2, pz.2⟩

theorem triangle_cases (edge : Sym2 (Fin 6) → Color) (x y z : Fin 6) (c : Color) :
    edge s(x, y) = c ∨ edge s(y, z) = c ∨ edge s(x, z) = c ∨
      (edge s(x, y) = c.opposite ∧ edge s(y, z) = c.opposite ∧
        edge s(x, z) = c.opposite) := by
  rcases color_cases (edge s(x, y)) c with hxy | hxy
  · exact Or.inl hxy
  rcases color_cases (edge s(y, z)) c with hyz | hyz
  · exact Or.inr (Or.inl hyz)
  rcases color_cases (edge s(x, z)) c with hxz | hxz
  · exact Or.inr (Or.inr (Or.inl hxz))
  exact Or.inr (Or.inr (Or.inr ⟨hxy, hyz, hxz⟩))

theorem triangle_two_color_exhaustive (edge : Sym2 (Fin 6) → Color)
    (c : Color) (x y z : Fin 6) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (∃ p q, (p = x ∨ p = y ∨ p = z) ∧ (q = x ∨ q = y ∨ q = z) ∧
      p ≠ q ∧ edge s(p, q) = c) ∨
    (edge s(x, y) = c.opposite ∧ edge s(y, z) = c.opposite ∧
      edge s(z, x) = c.opposite) := by
  rcases triangle_cases edge x y z c with h | h | h | h
  · exact Or.inl ⟨x, y, Or.inl rfl, Or.inr (Or.inl rfl), hxy, h⟩
  · exact Or.inl ⟨y, z, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hyz, h⟩
  · exact Or.inl ⟨x, z, Or.inl rfl, Or.inr (Or.inr rfl), hxz, h⟩
  · exact Or.inr ⟨h.1, h.2.1, by simpa [Sym2.eq_swap] using h.2.2⟩

theorem ramsey_six (edge : Sym2 (Fin 6) → Color) :
    ∃ x y c z, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      edge s(x, y) = c ∧ edge s(y, z) = c ∧ edge s(z, x) = c := by
  let v : Fin 6 := 0
  obtain ⟨x, c, y, z, hvx, hvy, hvz, hxy, hxz, hyz, evx, evy, evz⟩ :=
    pigeonhole_edges_at edge v
  rcases triangle_two_color_exhaustive edge c x y z hxy hyz hxz with
    ⟨p, q, hp, hq, hpq, epq⟩ | ⟨exy, eyz, ezx⟩
  · have hvp : v ≠ p := by rcases hp with rfl | rfl | rfl <;> assumption
    have hvq : v ≠ q := by rcases hq with rfl | rfl | rfl <;> assumption
    have evp : edge s(v, p) = c := by rcases hp with rfl | rfl | rfl <;> assumption
    have evq : edge s(v, q) = c := by rcases hq with rfl | rfl | rfl <;> assumption
    exact ⟨v, p, c, q, hvp, hpq, hvq, evp, epq, by simpa [Sym2.eq_swap] using evq⟩
  · exact ⟨x, y, c.opposite, z, hxy, hyz, hxz, exy, eyz, ezx⟩

def pentagon (x y : Fin 5) : Color :=
  if (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val then .red else .blue

def counterexample : Sym2 (Fin 5) → Color :=
  Sym2.lift ⟨pentagon, by intro x y; simp [pentagon, or_comm]⟩

theorem ramsey_five_counterexample : ¬ ∃ x y z, Monochromatic counterexample x y z := by
  unfold Monochromatic
  decide

theorem pattern_iff_ordinary (edge : Sym2 (Fin 6) → Color) :
    (∃ x y c z, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      edge s(x, y) = c ∧ edge s(y, z) = c ∧ edge s(z, x) = c) ↔ ∃ x y z, Monochromatic edge x y z := by
  constructor
  · rintro ⟨x, y, c, z, hxy, hyz, hxz, exy, eyz, ezx⟩
    exact ⟨x, y, z, hxy, hyz, hxz, c, exy, eyz, by simpa [Sym2.eq_swap] using ezx⟩
  · rintro ⟨x, y, z, hxy, hyz, hxz, c, exy, eyz, exz⟩
    exact ⟨x, y, c, z, hxy, hyz, hxz, exy, eyz, by simpa [Sym2.eq_swap] using exz⟩

end DesignExamples.PatternStyle.Ramsey
