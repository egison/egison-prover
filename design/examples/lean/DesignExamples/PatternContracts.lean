import DesignExamples.Ramsey

namespace DesignExamples.PatternContracts

def Star (edge : Sym2 (Fin 6) → Color) (v x y z : Fin 6) (c : Color) : Prop :=
  v ≠ x ∧ v ≠ y ∧ v ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    edge s(v, x) = c ∧ edge s(v, y) = c ∧ edge s(v, z) = c

theorem pigeonhole_edges_at (edge : Sym2 (Fin 6) → Color) (v : Fin 6) :
    ∃ x c y z, Star edge v x y z c := by
  obtain ⟨c, hc⟩ := Ramsey.pigeonhole_edges edge v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < (Ramsey.neighbors edge v c).card)
  have px := Finset.mem_filter.mp hx
  have py := Finset.mem_filter.mp hy
  have pz := Finset.mem_filter.mp hz
  exact ⟨x, c, y, z, (Finset.mem_erase.mp px.1).1.symm,
    (Finset.mem_erase.mp py.1).1.symm, (Finset.mem_erase.mp pz.1).1.symm,
    hxy, hxz, hyz, px.2, py.2, pz.2⟩

theorem color_cases (a c : Color) : a = c ∨ a = c.opposite := by
  by_cases h : a = c
  · exact Or.inl h
  · exact Or.inr (Color.eq_opposite_of_ne h)

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

/-- Ordinary Lean with the same star and internal-edge coverage lemmas. -/
theorem ramsey_six_shared_helpers (edge : Sym2 (Fin 6) → Color) :
    ∃ x y z, Ramsey.Monochromatic edge x y z := by
  let v : Fin 6 := 0
  obtain ⟨x, c, y, z, hvx, hvy, hvz, hxy, hxz, hyz, evx, evy, evz⟩ :=
    pigeonhole_edges_at edge v
  rcases triangle_two_color_exhaustive edge c x y z hxy hyz hxz with
    ⟨p, q, hp, hq, hpq, epq⟩ | ⟨exy, eyz, ezx⟩
  · have hvp : v ≠ p := by rcases hp with rfl | rfl | rfl <;> assumption
    have hvq : v ≠ q := by rcases hq with rfl | rfl | rfl <;> assumption
    have evp : edge s(v, p) = c := by rcases hp with rfl | rfl | rfl <;> assumption
    have evq : edge s(v, q) = c := by rcases hq with rfl | rfl | rfl <;> assumption
    exact ⟨v, p, q, hvp, hpq, hvq, c, evp, epq, evq⟩
  · exact ⟨x, y, z, hxy, hyz, hxz, c.opposite, exy, eyz,
      by simpa [Sym2.eq_swap] using ezx⟩

end DesignExamples.PatternContracts
