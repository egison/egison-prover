import DesignExamples.Common

namespace DesignExamples.Ramsey

def Monochromatic {n : Nat} (coloring : Sym2 (Fin n) → Color) (x y z : Fin n) : Prop :=
  x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    ∃ c, coloring s(x, y) = c ∧ coloring s(y, z) = c ∧ coloring s(x, z) = c

def neighbors (coloring : Sym2 (Fin 6) → Color) (v : Fin 6) (c : Color) : Finset (Fin 6) :=
  (Finset.univ.erase v).filter (fun w => coloring s(v, w) = c)

theorem neighbors_total (coloring : Sym2 (Fin 6) → Color) (v : Fin 6) :
    (neighbors coloring v .red).card + (neighbors coloring v .blue).card = 5 := by
  have hpartition : neighbors coloring v .red ∪ neighbors coloring v .blue = Finset.univ.erase v := by
    ext w
    simp only [neighbors, Finset.mem_union, Finset.mem_filter]
    cases coloring s(v, w) <;> simp
  have hdisjoint : Disjoint (neighbors coloring v .red) (neighbors coloring v .blue) := by
    rw [Finset.disjoint_left]
    intro w hr hb
    have hr' := (Finset.mem_filter.mp hr).2
    have hb' := (Finset.mem_filter.mp hb).2
    rw [hr'] at hb'
    cases hb'
  rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  simp

theorem pigeonhole_edges (coloring : Sym2 (Fin 6) → Color) (v : Fin 6) :
    ∃ c, 3 ≤ (neighbors coloring v c).card := by
  have ht := neighbors_total coloring v
  by_cases hr : 3 ≤ (neighbors coloring v .red).card
  · exact ⟨.red, hr⟩
  · exact ⟨.blue, by omega⟩

theorem ramsey_six (coloring : Sym2 (Fin 6) → Color) :
    ∃ x y z, Monochromatic coloring x y z := by
  let v : Fin 6 := 0
  obtain ⟨c, hc⟩ := pigeonhole_edges coloring v
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (neighbors coloring v c).card)
  have hvx := (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
  have hvy := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
  have hvz := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
  have evx := (Finset.mem_filter.mp hx).2
  have evy := (Finset.mem_filter.mp hy).2
  have evz := (Finset.mem_filter.mp hz).2
  by_cases hcx : coloring s(x, y) = c
  · exact ⟨v, x, y, hvx.symm, hxy, hvy.symm, c, evx, hcx, evy⟩
  by_cases hcy : coloring s(y, z) = c
  · exact ⟨v, y, z, hvy.symm, hyz, hvz.symm, c, evy, hcy, evz⟩
  by_cases hcz : coloring s(x, z) = c
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
