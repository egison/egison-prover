-- パターンの関係と各腕の推論を手動で展開した検査用の版。
import DesignExamples.Resolution

namespace DesignExamples.PatternStyle.Resolution

open DesignExamples.Resolution

variable {V : Type*}

theorem resolution_sound (σ : V → Prop) {C D R : Clause V} (h : Resolves C D R)
    (hC : ClauseHolds σ C) (hD : ClauseHolds σ D) : ClauseHolds σ R := by
  classical
  obtain ⟨p, xs, ys, hCeq, hDeq, hReq⟩ := h
  subst C D R
  rcases Classical.em (σ p) with hp | hp
  · apply (clause_add σ _ _).mpr
    right
    simpa [clause_cons, Holds, hp] using hD
  · apply (clause_add σ _ _).mpr
    left
    simpa [clause_cons, Holds, hp] using hC

theorem derivable_sound (σ : V → Prop) {F : Formula V} {C : Clause V}
    (h : Derivable F C) (hF : FormulaHolds σ F) : ClauseHolds σ C := by
  induction h with
  | assumption hmem => exact hF _ hmem
  | resolve hC hD hrel ihC ihD => exact resolution_sound σ hrel ihC ihD

theorem empty_clause_unsatisfiable {F : Formula V} (h : Derivable F 0) :
    ¬∃ σ, FormulaHolds σ F := by
  rintro ⟨σ, hF⟩
  have hc := derivable_sound σ h hF
  simp [ClauseHolds] at hc

theorem example_unsatisfiable : ¬∃ σ, FormulaHolds σ exampleFormula :=
  empty_clause_unsatisfiable example_derivation

end DesignExamples.PatternStyle.Resolution
