-- パターンの関係と証拠の除去を明示した Lean 版。提案ソースからの自動変換ではない。
-- 提案言語の完全なソース。記法と依存関係は ../../README.md を参照。
import DesignExamples.PatternStyle.Common

namespace DesignExamples.PatternStyle.Pumping

variable {Alpha Q : Type*} [Fintype Q]

def run (M : DFA Alpha Q) (w : List Alpha) : List Q :=
  (List.range (w.length + 1)).map (fun i => M.evalFrom M.start (w.take i))

def repeatWord (y : List Alpha) (k : Nat) : List Alpha :=
  (List.replicate k y).flatten

def IsPumpingDecomposition (M : DFA Alpha Q) (w x y z : List Alpha) : Prop :=
  w = x ++ y ++ z ∧ y ≠ [] ∧ x.length + y.length ≤ Fintype.card Q ∧
    ∀ k, x ++ repeatWord y k ++ z ∈ M.accepts

theorem run_repeats_state (M : DFA Alpha Q) (w : List Alpha)
    (hlen : Fintype.card Q ≤ w.length) :
    ∃ pre q mid post,
      (run M w).take (Fintype.card Q + 1) = pre ++ q :: (mid ++ q :: post) := by
  apply repeated_split
  intro hn
  have hb := hn.length_le_card
  simp only [List.length_take, run, List.length_map, List.length_range] at hb
  omega

theorem split_to_loop (M : DFA Alpha Q) (w : List Alpha) (pre : List Q) (q : Q)
    (mid post : List Q) (hlen : Fintype.card Q ≤ w.length)
    (hsplit : (run M w).take (Fintype.card Q + 1) = pre ++ q :: (mid ++ q :: post)) :
    ∃ x y z, w = x ++ y ++ z ∧ x.length + y.length ≤ Fintype.card Q ∧
      y ≠ [] ∧ M.evalFrom M.start x = q ∧ M.evalFrom q y = q ∧
      M.evalFrom q z = M.evalFrom M.start w := by
  let i := pre.length
  let j := pre.length + mid.length + 1
  have hlength := congrArg List.length hsplit
  simp only [List.length_take, run, List.length_map, List.length_range,
    List.length_append, List.length_cons] at hlength
  have hi : i < j := by dsimp [i, j]; omega
  have hj : j < Fintype.card Q + 1 := by dsimp [j]; omega
  have hij : i < Fintype.card Q + 1 := hi.trans hj
  have hjw : j ≤ w.length := by omega
  have ei : ((run M w).take (Fintype.card Q + 1))[i]? = some q := by
    rw [hsplit, List.getElem?_append_right (by dsimp [i]; omega)]
    simp [i]
  have ej : ((run M w).take (Fintype.card Q + 1))[j]? = some q := by
    rw [hsplit, List.getElem?_append_right (by dsimp [j]; omega)]
    have he : j - pre.length = mid.length + 1 := by dsimp [j]; omega
    rw [he]
    simp
  have eval_i : M.evalFrom M.start (w.take i) = q := by
    rw [List.getElem?_take_of_lt hij, run, List.getElem?_map,
      List.getElem?_range (by omega)] at ei
    exact Option.some.inj ei
  have eval_j : M.evalFrom M.start (w.take j) = q := by
    rw [List.getElem?_take_of_lt hj, run, List.getElem?_map,
      List.getElem?_range (by omega)] at ej
    exact Option.some.inj ej
  have ht : (w.take j).take i = w.take i := by
    rw [List.take_take, min_eq_left (Nat.le_of_lt hi)]
  refine ⟨w.take i, (w.take j).drop i, w.drop j, ?_, ?_, ?_, eval_i, ?_, ?_⟩
  · rw [← ht, List.take_append_drop, List.take_append_drop]
  · simp only [List.length_take, List.length_drop]
    omega
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_drop, List.length_take, List.length_nil] at hl
    omega
  · rw [← eval_i, ← ht, ← DFA.evalFrom_of_append, List.take_append_drop]
    rw [ht, eval_i]
    exact eval_j
  · rw [← eval_j, ← DFA.evalFrom_of_append, List.take_append_drop]

omit [Fintype Q] in
theorem loop_iteration (M : DFA Alpha Q) (q : Q) (y : List Alpha)
    (hloop : M.evalFrom q y = q) (k : Nat) :
    M.evalFrom q (repeatWord y k) = q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [repeatWord, List.replicate_succ, List.flatten_cons,
      DFA.evalFrom_of_append, hloop]
    exact ih

theorem pumping_lemma (M : DFA Alpha Q) (w : List Alpha)
    (hacc : w ∈ M.accepts) (hlen : Fintype.card Q ≤ w.length) :
    ∃ x y z, IsPumpingDecomposition M w x y z := by
  obtain ⟨pre, q, mid, post, hsplit⟩ := run_repeats_state M w hlen
  obtain ⟨x, y, z, heq, hbound, hne, hx, hy, hz⟩ :=
    split_to_loop M w pre q mid post hlen hsplit
  refine ⟨x, y, z, heq, hne, hbound, ?_⟩
  intro k
  change M.evalFrom M.start (x ++ repeatWord y k ++ z) ∈ M.accept
  rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hx,
    loop_iteration M q y hy k, hz]
  exact hacc

end DesignExamples.PatternStyle.Pumping
