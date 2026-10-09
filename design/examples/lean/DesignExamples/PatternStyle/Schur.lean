-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.Schur

def graph (c : D → Color) : Finset (Nat × Color) :=
  Finset.univ.image (fun d => (d.val, c d))

theorem mem_graph (c : D → Color) (d : D) : (d.val, c d) ∈ graph c :=
  Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩

def Monochromatic (c : D → Color) (x y z : D) : Prop :=
  ∃ col, c x = col ∧ c y = col ∧ c z = col ∧ x.val + y.val = z.val

theorem schur_two (c : D → Color) :
    ∃ x col y, (x, col) ∈ graph c ∧ (y, col) ∈ graph c ∧ (x+y, col) ∈ graph c := by
  obtain ⟨col, h1⟩ := at_key c D.one
  rcases color_cases (c D.two) col with h2 | h2
  · refine ⟨1, col, 1, ?_⟩
    simpa [D.val, h1, h2] using
      And.intro (mem_graph c .one) (And.intro (mem_graph c .one) (mem_graph c .two))
  · rcases color_cases (c D.four) col.opposite with h4 | h4
    · refine ⟨2, col.opposite, 2, ?_⟩
      simpa [D.val, h2, h4] using
        And.intro (mem_graph c .two) (And.intro (mem_graph c .two) (mem_graph c .four))
    · have h4 : c D.four = col := by simpa using h4
      rcases color_cases (c D.five) col with h5 | h5
      · refine ⟨1, col, 4, ?_⟩
        simpa [D.val, h1, h4, h5] using
          And.intro (mem_graph c .one) (And.intro (mem_graph c .four) (mem_graph c .five))
      · rcases color_cases (c D.three) col.opposite with h3 | h3
        · refine ⟨2, col.opposite, 3, ?_⟩
          simpa [D.val, h2, h3, h5] using
            And.intro (mem_graph c .two) (And.intro (mem_graph c .three) (mem_graph c .five))
        · have h3 : c D.three = col := by simpa using h3
          refine ⟨1, col, 3, ?_⟩
          simpa [D.val, h1, h3, h4] using
            And.intro (mem_graph c .one) (And.intro (mem_graph c .three) (mem_graph c .four))

def counterexample (x : Fin 4) : Color := if x.val = 0 ∨ x.val = 3 then .red else .blue

theorem schur_four_counterexample :
    ¬ ∃ x y z : Fin 4, counterexample x = counterexample y ∧
      counterexample y = counterexample z ∧ (x.val + 1) + (y.val + 1) = z.val + 1 := by
  decide

theorem pattern_iff_ordinary (c : D → Color) :
    (∃ x col y, (x, col) ∈ graph c ∧ (y, col) ∈ graph c ∧ (x+y, col) ∈ graph c) ↔ ∃ x y z, Monochromatic c x y z := by
  constructor
  · rintro ⟨x, col, y, hx, hy, hz⟩
    obtain ⟨dx, _, hx⟩ := Finset.mem_image.mp hx
    obtain ⟨dy, _, hy⟩ := Finset.mem_image.mp hy
    obtain ⟨dz, _, hz⟩ := Finset.mem_image.mp hz
    simp only [Prod.mk.injEq] at hx hy hz
    exact ⟨dx, dy, dz, col, hx.2, hy.2, hz.2, by omega⟩
  · rintro ⟨dx, dy, dz, col, hx, hy, hz, hsum⟩
    refine ⟨dx.val, col, dy.val, ?_, ?_, ?_⟩
    · simpa [hx] using mem_graph c dx
    · simpa [hy] using mem_graph c dy
    · rw [hsum]
      simpa [hz] using mem_graph c dz

end DesignExamples.PatternStyle.Schur
