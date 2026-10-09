import DesignExamples.Common

namespace DesignExamples.Ramsey

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

theorem ramsey_six (edge : Sym2 (Fin 6) → Color) :
    ∃ x y z, Monochromatic edge x y z := by
  let v : Fin 6 := 0
  obtain ⟨c, hc⟩ := pigeonhole_edges edge v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (neighbors edge v c).card)
  have hvx := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
  have hvy := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
  have hvz := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
  have evx := (Finset.mem_filter.mp hx).2
  have evy := (Finset.mem_filter.mp hy).2
  have evz := (Finset.mem_filter.mp hz).2
  by_cases hcx : edge s(x, y) = c
  · exact ⟨v, x, y, hvx.symm, hxy, hvy.symm, c, evx, hcx, evy⟩
  by_cases hcy : edge s(y, z) = c
  · exact ⟨v, y, z, hvy.symm, hyz, hvz.symm, c, evy, hcy, evz⟩
  by_cases hcz : edge s(x, z) = c
  · exact ⟨v, x, z, hvx.symm, hxz, hvz.symm, c, evx, hcz, evz⟩
  exact ⟨x, y, z, hxy, hyz, hxz, c.opposite,
    Color.eq_opposite_of_ne hcx, Color.eq_opposite_of_ne hcy, Color.eq_opposite_of_ne hcz⟩

def pentagon (x y : Fin 5) : Color :=
  if (x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val then .red else .blue

def counterexample : Sym2 (Fin 5) → Color :=
  Sym2.lift ⟨pentagon, by intro x y; simp [pentagon, or_comm]⟩

theorem ramsey_five_counterexample : ¬ ∃ x y z, Monochromatic counterexample x y z := by
  unfold Monochromatic
  decide

end DesignExamples.Ramsey
