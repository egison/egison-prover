import DesignExamples.Alternating
import DesignExamples.PatternStyle.Alternating

-- This audit intentionally imports only the new example, not the Ramsey modules
-- (which import all of Mathlib). A library proof of alternating-group simplicity
-- must not be available to the proofs checked here.
open Lean in
run_cmd do
  let env ← getEnv
  for n in #[`alternatingGroup.isSimpleGroup,
      `alternatingGroup.isSimpleGroup_five,
      `alternatingGroup.normal_subgroup_eq_bot_or_eq_top] do
    if env.contains n then
      throwError "The example imported a library simplicity theorem: {n}"
  for n in #[`DesignExamples.Alternating.cases_exhaustive,
      `DesignExamples.Alternating.matchingCases_iff_cases,
      `DesignExamples.Alternating.Ordinary.alternating_simple,
      `DesignExamples.Alternating.PatternStyle.alternating_simple] do
    for ax in (← collectAxioms n) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom in {n}: {ax}"

#print axioms DesignExamples.Alternating.cycle3_isThreeCycle
#print axioms DesignExamples.Alternating.cycle3_even
#print axioms DesignExamples.Alternating.conjugate_cycle3
#print axioms DesignExamples.Alternating.comm_cycle3
#print axioms DesignExamples.Alternating.comm_mem
#print axioms DesignExamples.Alternating.comm_path4
#print axioms DesignExamples.Alternating.comm_three_extra
#print axioms DesignExamples.Alternating.orbit_at_cases
#print axioms DesignExamples.Alternating.cases_exhaustive
#print axioms DesignExamples.Alternating.cycle5_path
#print axioms DesignExamples.Alternating.two_pairs_comm_fixed
#print axioms DesignExamples.Alternating.two_pairs_comm_moved
#print axioms DesignExamples.Alternating.exists_fifth
#print axioms DesignExamples.Alternating.three_of_path4
#print axioms DesignExamples.Alternating.three_of_three_extra
#print axioms DesignExamples.Alternating.three_of_two_pairs
#print axioms DesignExamples.Alternating.eq_alternating_of_three
#print axioms DesignExamples.Alternating.simple_of_three_cycle_production
#print axioms DesignExamples.Alternating.onlyThreeMatch_iff
#print axioms DesignExamples.Alternating.path4Match_iff
#print axioms DesignExamples.Alternating.threeExtraMatch_iff
#print axioms DesignExamples.Alternating.twoPairsMatch_iff
#print axioms DesignExamples.Alternating.matchingCases_iff_cases
#print axioms DesignExamples.Alternating.matching_cases_exhaustive
#print axioms DesignExamples.Alternating.Ordinary.contains_three
#print axioms DesignExamples.Alternating.Ordinary.alternating_simple
#print axioms DesignExamples.Alternating.Ordinary.a5_simple
#print axioms DesignExamples.Alternating.PatternStyle.contains_three
#print axioms DesignExamples.Alternating.PatternStyle.alternating_simple
#print axioms DesignExamples.Alternating.PatternStyle.a5_simple

-- The two explicit A₅ calculations used in the motivating three-case proof.
open Equiv DesignExamples.Alternating in
example : comm (cycle5 (0 : Fin 5) 1 2 3 4) (cycle3 0 1 2) = cycle3 0 3 1 := by
  decide

open Equiv DesignExamples.Alternating in
example : comm (swap (0 : Fin 5) 1 * swap 2 3) (cycle3 0 2 4) =
    cycle5 0 1 3 4 2 := by
  decide
