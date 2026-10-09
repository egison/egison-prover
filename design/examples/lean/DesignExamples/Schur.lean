import DesignExamples.Common

namespace DesignExamples.Schur

def graph (c : D → Color) : Finset (Nat × Color) :=
  Finset.univ.image (fun d => (d.val, c d))

theorem mem_graph (c : D → Color) (d : D) : (d.val, c d) ∈ graph c :=
  Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

def Monochromatic (c : D → Color) (x y z : D) : Prop :=
  ∃ col, c x = col ∧ c y = col ∧ c z = col ∧ x.val + y.val = z.val

theorem schur_two (c : D → Color) : ∃ x y z, Monochromatic c x y z := by
  let col := c .one
  by_cases h2 : c .two = col
  · exact ⟨.one, .one, .two, col, rfl, rfl, h2, rfl⟩
  have h2' := Color.eq_opposite_of_ne h2
  by_cases h4 : c .four = col.opposite
  · exact ⟨.two, .two, .four, col.opposite, h2', h2', h4, rfl⟩
  have h4' : c .four = col := by
    have h := Color.eq_opposite_of_ne h4
    simpa using h
  by_cases h5 : c .five = col
  · exact ⟨.one, .four, .five, col, rfl, h4', h5, rfl⟩
  have h5' := Color.eq_opposite_of_ne h5
  by_cases h3 : c .three = col.opposite
  · exact ⟨.two, .three, .five, col.opposite, h2', h3, h5', rfl⟩
  have h3' : c .three = col := by
    have h := Color.eq_opposite_of_ne h3
    simpa using h
  exact ⟨.one, .three, .four, col, rfl, h3', h4', rfl⟩

def counterexample (x : Fin 4) : Color := if x.val = 0 ∨ x.val = 3 then .red else .blue

theorem schur_four_counterexample :
    ¬ ∃ x y z : Fin 4, counterexample x = counterexample y ∧
      counterexample y = counterexample z ∧ (x.val + 1) + (y.val + 1) = z.val + 1 := by
  decide

end DesignExamples.Schur
