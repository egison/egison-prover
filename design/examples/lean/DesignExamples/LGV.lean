/-
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
Adapted from faabian/algebraic-combinatorics, AlgebraicCombinatorics/Determinants/LGV2.lean.
Source: https://github.com/faabian/algebraic-combinatorics/tree/3b333089a7a7cd6478065fcfbd91c2b566fccac0
License: CC BY-NC 4.0; see design/examples/LICENSE-AlgebraicCombinatorics.
The copied and adapted LGV proofs retain that license, separately from the other examples.
-/
import DesignExamples.LGVCommon

set_option backward.isDefEq.respectTransparency false

open Finset BigOperators Matrix
namespace DesignExamples.LGV
variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

/-- The sign-reversing involution on intersecting path tuples.
    For an ipat (σ, 𝐩), we:
    1. Find the smallest i such that p_i contains a crowded point
    2. Find the first crowded point v on p_i
    3. Find the largest j such that v is on p_j
    4. Exchange tails of p_i and p_j at v
    5. Compose σ with the transposition t_{i,j}
    This gives (σ ∘ t_{i,j}, 𝐩') which is still an ipat.

    **Implementation note:** The permutation component is `sp.1 * Equiv.swap i j` where
    i and j are the intersection indices. The path tuple component uses `exchangeTails`
    to swap the tails of paths i and j at the crowded vertex v. -/
noncomputable def signReversing {D : SimpleDigraph V} (_hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) : pathTupleWithPerm (D := D) A B :=
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  let newPaths : Fin k → SimpleDigraph.Path D := fun l =>
    if h : l = i then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1
    else if h' : l = j then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2
    else sp.2.paths l
  have h_starts : ∀ l, (newPaths l).start = A l := by
    intro l
    simp only [newPaths]
    split_ifs with h h'
    · rw [h, exchangeTails_fst_start, sp.2.starts]
    · rw [h', exchangeTails_snd_start, sp.2.starts]
    · exact sp.2.starts l
  have h_finishes : ∀ l, (newPaths l).finish = (permuteKVertex (sp.1 * Equiv.swap i j) B) l := by
    intro l
    simp only [newPaths, permuteKVertex, Equiv.Perm.coe_mul, Function.comp_apply]
    split_ifs with h h'
    · -- l = i case
      rw [h, exchangeTails_fst_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_left]
    · -- l = j case
      rw [h', exchangeTails_snd_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_right]
    · -- l ≠ i, l ≠ j case
      rw [sp.2.finishes]
      simp only [permuteKVertex]
      congr 1
      rw [Equiv.swap_apply_of_ne_of_ne h h']
    ⟨sp.1 * Equiv.swap i j, ⟨newPaths, h_starts, h_finishes⟩⟩

/-- The signReversing map preserves the intersecting property.
    The crowded point v at indices i and j is preserved in the exchanged paths. -/
lemma signReversing_isIntersecting {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    (signReversing hac sp hip).2.isIntersecting := by
  -- Extract the intersection data used by signReversing
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Show v is a crowded point in the new paths at indices i and j
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  use v
  unfold PathTuple.isCrowded
  use i, j, hij
  constructor
  · -- v is in path i of sp'
    show v ∈ ((signReversing hac sp hip).2.paths i).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · -- v is in path j of sp'
    show v ∈ ((signReversing hac sp hip).2.paths j).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj

/-- Helper: The paths of sp' at index i is the first component of exchangeTails -/
lemma signReversing_path_i {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]

/-- Helper: The paths of sp' at index j is the second component of exchangeTails -/
lemma signReversing_path_j {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]

/-- Helper: The paths of sp' at index l ≠ i, j are unchanged -/
lemma signReversing_path_other {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (l : Fin k) (hl_ne_i : l ≠ i) (hl_ne_j : l ≠ j) :
    (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- Helper: The permutation of sp' is sp.1 * swap i j -/
lemma signReversing_perm_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  conv_lhs => unfold signReversing; rw [h_data]

/-- Helper: A vertex w is in the head of path p (before v) iff it's in the head of the exchanged path -/
lemma mem_head_iff_mem_exchangeTails_head {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v w : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let hv_p' := exchangeTails_fst_mem_v p q v hv_p hv_q
    w ∈ (p.splitAt v hv_p).1.vertices ↔ w ∈ (p'.splitAt v hv_p').1.vertices := by
  simp only
  rw [exchangeTails_head_eq _hac p q v hv_p hv_q]

/-- Helper: exchangeTails preserves head vertices (snd version) -/
lemma exchangeTails_head_eq_snd {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let q' := (exchangeTails p q v hv_p hv_q).2
    let hv_q' := exchangeTails_snd_mem_v p q v hv_p hv_q
    (q'.splitAt v hv_q').1.vertices = (q.splitAt v hv_q).1.vertices := by
  simp only
  rw [splitAt_fst_vertices, splitAt_fst_vertices]
  rw [exchangeTails_snd_vertices]
  -- The head of q' = head_q ++ tail_p.tail is just head_q (up to v)
  have h_head_q := splitAt_fst_vertices q v hv_q
  have h_tail_p := splitAt_snd_vertices p v hv_p
  have h_head_q_last : (q.splitAt v hv_q).1.vertices.getLast (q.splitAt v hv_q).1.nonempty = v :=
    SimpleDigraph.Path.splitAt_head_finish q v hv_q
  have h_findIdx_head : (q.splitAt v hv_q).1.vertices.findIdx (· = v) =
      (q.splitAt v hv_q).1.vertices.length - 1 := splitAt_head_findIdx_eq q.vertices v hv_q
  have h_concat := splitAt_concat_vertices_eq
    (q.splitAt v hv_q).1.vertices (p.splitAt v hv_p).2.vertices v
    (q.splitAt v hv_q).1.nonempty (p.splitAt v hv_p).2.nonempty
    h_head_q_last (SimpleDigraph.Path.splitAt_tail_start p v hv_p)
    h_findIdx_head
  simp only at h_concat
  exact congr_arg Prod.fst h_concat

/-- Key invariance lemma: pathIndicesContaining v is preserved after signReversing.
    This holds because v is in the HEAD of paths i and j (since v is the first crowded vertex
    on path i, and v is shared with j). After exchangeTails at v, the heads are preserved,
    so v is still on exactly the same paths. -/
lemma signReversing_pathIndicesContaining_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.pathIndicesContaining v = sp.2.pathIndicesContaining v := by
  ext l
  simp only [PathTuple.pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
  -- We need to show: v ∈ sp'.paths l ↔ v ∈ sp.paths l
  by_cases hl_i : l = i
  · -- l = i case
    constructor
    · intro hv_sp'
      rw [hl_i]
      exact hvi
    · intro _
      rw [hl_i, signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
      exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · by_cases hl_j : l = j
    · -- l = j case
      constructor
      · intro hv_sp'
        rw [hl_j]
        exact hvj
      · intro _
        rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
        exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
    · -- l ≠ i, l ≠ j case: path l is unchanged
      rw [signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_i hl_j]

/-- Helper lemma: findIdx returns n if the element at position n satisfies the predicate
    and all elements before it do not. -/
lemma findIdx_eq_of_first {α : Type*} (l : List α) (p : α → Bool)
    (n : ℕ) (hn : n < l.length)
    (h_first : ∀ m : ℕ, ∀ hm : m < n, ¬p (l[m]'(Nat.lt_trans hm hn)))
    (h_p_n : p (l[n]'hn)) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.findIdx_cons, List.getElem_cons_zero] at h_p_n ⊢
      simp [h_p_n]
    | succ n' =>
      simp only [List.findIdx_cons]
      have h_not_x : p x = false := by
        have := h_first 0 (Nat.zero_lt_succ n')
        simp at this
        exact this
      simp only [h_not_x, cond_false]
      have hn' : n' < xs.length := by simp at hn; omega
      have h_first' : ∀ m : ℕ, ∀ hm : m < n', ¬p (xs[m]'(Nat.lt_trans hm hn')) := by
        intro m hm
        have hm1 : m + 1 < n' + 1 := by omega
        have := h_first (m + 1) hm1
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_p_n' : p (xs[n']'hn') := by
        have := h_p_n
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_ih := ih n' hn' h_first' h_p_n'
      omega

/-- Helper lemma: vertices before v on path i are not crowded in sp'.
    This is the key insight for proving that firstCrowdedIndexOnPath is preserved.

    For any vertex w at index m < idx on path i (where idx is the index of v):
    - w is not crowded in sp (since v at idx is the FIRST crowded vertex)
    - w is only on path i in sp (not on any other path)
    - After exchangeTails, w is still only on path i:
      * w is in the head of path i (preserved by exchangeTails_head_eq)
      * w is not in path j' = head_j ++ tail_i.tail (w not in head_j since not in path j,
        and w not in tail_i.tail since w is before v which starts tail_i)
      * w is not in any other path l (paths l are unchanged for l ≠ i, j)
    - So w is not crowded in sp' -/
lemma vertices_before_v_not_crowded_in_sp' {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (w : V) (m : ℕ) (hm_lt_idx : m < (sp.2.paths i).vertices.findIdx (· = v))
    (hm_lt_len : m < (sp.2.paths i).vertices.length)
    (hw_eq : (sp.2.paths i).vertices[m] = w) :
    w ∉ (signReversing hac sp hip).2.crowdedVerticesOnPath i := by
  -- Step 1: Show w is NOT crowded in sp (since v is the first crowded vertex)
  -- This means w is only on path i in sp, not shared with any other path

  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩

  -- From h_data, i is the min of crowdedPathIndices
  have hi_min_sp : i = sp.2.crowdedPathIndices.min'
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm

  -- v is at position firstCrowdedIndexOnPath i
  have h_v_at_idx : (sp.2.paths i).vertices[sp.2.firstCrowdedIndexOnPath i]'
      (sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded) = v := by
    -- Extract from getCanonicalIntersectionData definition
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    -- The equality gives us that v is the vertex at firstCrowdedIndexOnPath i
    have h_eq := congrArg (fun x => x.val.2.2.val) h
    simp only [List.get_eq_getElem] at h_eq
    -- h_eq says v = (paths i').vertices[firstCrowdedIndexOnPath i']
    -- where i' = crowdedPathIndices.min'
    -- Since i = i' (from hi_min_sp), we can use simp with hi_min_sp
    simp only [← hi_min_sp] at h_eq
    exact h_eq

  -- Since paths have nodup vertices (acyclic), findIdx (· = v) = firstCrowdedIndexOnPath i
  have hnd := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
  have h_findIdx_eq : (sp.2.paths i).vertices.findIdx (· = v) = sp.2.firstCrowdedIndexOnPath i := by
    have h_idx : (sp.2.paths i).vertices.idxOf v = sp.2.firstCrowdedIndexOnPath i := by
      rw [← h_v_at_idx]
      exact hnd.idxOf_getElem _ _
    simp only [List.idxOf] at h_idx
    exact h_idx

  -- Therefore m < firstCrowdedIndexOnPath i
  have hm_lt_first : m < sp.2.firstCrowdedIndexOnPath i := by
    rw [← h_findIdx_eq]
    exact hm_lt_idx

  -- So w = (paths i).vertices[m] is NOT in crowdedVerticesOnPath i
  -- (because firstCrowdedIndexOnPath is the FIRST index where the crowded predicate holds)
  have hw_not_crowded_sp : w ∉ sp.2.crowdedVerticesOnPath i := by
    rw [← hw_eq]
    -- The predicate for crowdedVerticesOnPath is decidable
    have h_pred : ¬ ((sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i) := by
      intro h_in
      -- firstCrowdedIndexOnPath i = findIdx (fun v => v ∈ crowdedVerticesOnPath i)
      unfold PathTuple.firstCrowdedIndexOnPath at hm_lt_first
      -- If (paths i).vertices[m] ∈ crowdedVerticesOnPath i, then findIdx should be ≤ m
      have h_findIdx_le : (sp.2.paths i).vertices.findIdx
          (fun v => v ∈ sp.2.crowdedVerticesOnPath i) ≤ m := by
        -- If the element at position m satisfies the predicate, then findIdx ≤ m
        have hp : (sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i := h_in
        -- Use the fact that findIdx returns the first index satisfying the predicate
        -- If element at m satisfies it, findIdx must be ≤ m
        by_contra h_gt
        push Not at h_gt
        -- All elements before findIdx don't satisfy the predicate
        -- In particular, element at m doesn't satisfy it (since m < findIdx)
        have h_not_p : ¬ (fun v => v ∈ sp.2.crowdedVerticesOnPath i) (sp.2.paths i).vertices[m] := by
          have h_lt : m < (sp.2.paths i).vertices.findIdx (fun v => v ∈ sp.2.crowdedVerticesOnPath i) := h_gt
          -- For all n < findIdx, the element at n doesn't satisfy the predicate
          have := List.not_of_lt_findIdx h_lt
          simp only [decide_eq_false_iff_not] at this
          exact this
        exact h_not_p hp
      omega
    exact h_pred

  -- This means w is only on path i in sp (not shared with any other path)
  have hw_only_on_i : ∀ l : Fin k, l ≠ i → w ∉ (sp.2.paths l).vertices := by
    intro l hl
    by_contra hw_l
    apply hw_not_crowded_sp
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rw [← hw_eq]; exact List.getElem_mem hm_lt_len
    · exact ⟨l, hl.symm, hw_l⟩

  -- Step 2: Show w is not crowded in sp'
  -- w ∉ sp'.crowdedVerticesOnPath i means:
  -- either w ∉ sp'.paths i, or ∀ l ≠ i, w ∉ sp'.paths l
  -- We'll show the second

  simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, not_and]
  intro hw_in_sp'_i
  push Not
  intro l hl

  -- Case analysis on l
  by_cases hl_j : l = j
  · -- l = j: w is not on path j in sp', which is head_j ++ tail_i.tail
    rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    rw [exchangeTails_snd_vertices]
    simp only [List.mem_append, not_or]
    constructor
    · -- w not in head_j (= take part of path j up to v)
      -- Since w is only on path i in sp, w ∉ path j in sp
      have hw_not_j := hw_only_on_i j hij.symm
      intro hw_head_j
      apply hw_not_j
      have := splitAt_fst_vertices (sp.2.paths j) v hvj
      rw [this] at hw_head_j
      exact List.mem_of_mem_take hw_head_j
    · -- w not in tail_i.tail (= drop part of path i after v)
      -- Since w is at position m < findIdx(v), w is before v on path i
      -- So w cannot be in tail_i.tail (which starts after v)
      intro hw_tail_i
      -- w is at position m < findIdx(v), so w is in take (findIdx(v)+1)
      -- But tail starts at findIdx(v), so tail.tail starts at findIdx(v)+1
      -- By nodup, w cannot be in both take(findIdx(v)+1) and drop(findIdx(v)+1)
      have h_w_in_take : w ∈ (sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        have h_take_len : m < ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).length := by
          simp only [List.length_take]
          omega
        have := List.getElem_mem h_take_len
        simp only [List.getElem_take] at this
        rw [hw_eq] at this
        exact this
      have h_tail_drop : ((sp.2.paths i).splitAt v hvi).2.vertices.tail =
          (sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        rw [splitAt_snd_vertices]
        exact List.tail_drop
      rw [h_tail_drop] at hw_tail_i
      have h_disjoint : ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).Disjoint
          ((sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1)) :=
        List.disjoint_take_drop hnd (Nat.le_refl _)
      exact List.disjoint_left.mp h_disjoint h_w_in_take hw_tail_i
  · -- l ≠ j (and l ≠ i by hl)
    -- Path l is unchanged in sp'
    have h_path_l_eq : (signReversing hac sp hip).2.paths l = sp.2.paths l :=
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl.symm hl_j
    rw [h_path_l_eq]
    exact hw_only_on_i l hl.symm

/-- Key invariance lemma: The canonical selection returns the same (i, j, v) for sp' as for sp.
    This is the heart of the involutive proof. -/
lemma signReversing_canonical_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (hip' : (signReversing hac sp hip).2.isIntersecting) :
    ∃ hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices,
    ∃ hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices,
    getCanonicalIntersectionData (signReversing hac sp hip).2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩ := by
  -- The membership facts for v in sp'
  have hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices := by
    rw [signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices := by
    rw [signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  use hvi', hvj'

  -- We need to show that getCanonicalIntersectionData returns the same (i, j, v)
  -- This requires showing:
  -- 1. i = sp'.2.crowdedPathIndices.min'
  -- 2. v = sp'.2.paths i at firstCrowdedIndexOnPath
  -- 3. j = (sp'.2.pathIndicesContaining v \ {i}).max'

  -- The key insight is that v is the FIRST crowded vertex on path i.
  -- After exchangeTails, the head of path i (vertices up to and including v) is preserved.
  -- Therefore:
  -- - v is still crowded on path i (shared with j, whose head also contains v)
  -- - All vertices before v on path i are still not crowded
  -- - So v is still the first crowded vertex on path i
  -- - i is still the smallest crowded index (any smaller index has unchanged path)
  -- - pathIndicesContaining v is preserved (shown above)
  -- - So j is still the largest in pathIndicesContaining v \ {i}

  -- Set up sp' for convenience
  set sp' := signReversing hac sp hip with h_sp'

  -- First, establish that i is in sp'.2.crowdedPathIndices
  have hi'_crowded : i ∈ sp'.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi', hvj'⟩

  -- Extract that i was the min for sp
  have hi_min_sp : i = sp.2.crowdedPathIndices.min'
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm

  -- Show that no index < i is crowded in sp'
  -- This is the key case analysis: for any l < i, l was not crowded in sp,
  -- and after signReversing, l is still not crowded because:
  -- - If l ∉ {i, j}, path l is unchanged
  -- - If l = j, then j < i, but j is crowded (shares v with i), so j ≥ i, contradiction
  have h_no_smaller_crowded : ∀ l : Fin k, l < i → l ∉ sp'.2.crowdedPathIndices := by
    intro l hl_lt
    have hl_not_crowded_sp : l ∉ sp.2.crowdedPathIndices := by
      intro hl_in
      have h_le := Finset.min'_le sp.2.crowdedPathIndices l hl_in
      rw [← hi_min_sp] at h_le
      omega
    -- Case analysis: is l = j?
    by_cases hlj : l = j
    · -- Case l = j: This is a contradiction
      -- j is crowded in sp (shares v with i), so j ∈ crowdedPathIndices
      -- Since i is the minimum, i ≤ j. But l = j < i, contradiction.
      have hj_crowded : j ∈ sp.2.crowdedPathIndices := by
        simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        use i, hij.symm
        simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
        exact ⟨v, hvj, hvi⟩
      have hi_le_j := Finset.min'_le sp.2.crowdedPathIndices j hj_crowded
      rw [← hi_min_sp] at hi_le_j
      omega
    · -- Case l ≠ j (and l ≠ i since l < i)
      have hli : l ≠ i := by omega
      -- Path l is unchanged in sp'
      have h_path_l_eq : sp'.2.paths l = sp.2.paths l :=
        signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hli hlj
      -- Suppose l is crowded in sp'. Then there exists m ≠ l with shared vertex w.
      intro hl_crowded'
      simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hl_crowded'
      obtain ⟨m, hlm, w, hw_inter⟩ := hl_crowded'
      simp only [Finset.mem_inter, List.mem_toFinset] at hw_inter
      obtain ⟨hw_l', hw_m'⟩ := hw_inter
      -- w is on path l in sp' = path l in sp
      rw [h_path_l_eq] at hw_l'
      -- Case analysis on m
      by_cases hmi : m = i
      · -- m = i: w is on path l (unchanged) and path i' = head_i ++ tail_j.tail
        rw [hmi, signReversing_path_i hac sp hip i j hij v hvi hvj h_data] at hw_m'
        rw [exchangeTails_fst_vertices] at hw_m'
        simp only [List.mem_append] at hw_m'
        rcases hw_m' with hw_head_i | hw_tail_j
        · -- w is in head_i: w was on path l and path i in sp
          have hw_i : w ∈ (sp.2.paths i).vertices := by
            have := splitAt_fst_vertices (sp.2.paths i) v hvi
            rw [this] at hw_head_i
            exact List.mem_of_mem_take hw_head_i
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- w is in tail_j.tail: w was on path l and path j in sp
          have hw_j : w ∈ (sp.2.paths j).vertices := by
            have := splitAt_snd_vertices (sp.2.paths j) v hvj
            rw [this] at hw_tail_j
            exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_j)
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
      · by_cases hmj : m = j
        · -- m = j: w is on path l (unchanged) and path j' = head_j ++ tail_i.tail
          rw [hmj, signReversing_path_j hac sp hip i j hij v hvi hvj h_data] at hw_m'
          rw [exchangeTails_snd_vertices] at hw_m'
          simp only [List.mem_append] at hw_m'
          rcases hw_m' with hw_head_j | hw_tail_i
          · -- w is in head_j: w was on path l and path j in sp
            have hw_j : w ∈ (sp.2.paths j).vertices := by
              have := splitAt_fst_vertices (sp.2.paths j) v hvj
              rw [this] at hw_head_j
              exact List.mem_of_mem_take hw_head_j
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
          · -- w is in tail_i.tail: w was on path l and path i in sp
            have hw_i : w ∈ (sp.2.paths i).vertices := by
              have := splitAt_snd_vertices (sp.2.paths i) v hvi
              rw [this] at hw_tail_i
              exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_i)
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- m ∉ {i, j}: path m is unchanged
          have h_path_m_eq : sp'.2.paths m = sp.2.paths m :=
            signReversing_path_other hac sp hip i j hij v hvi hvj h_data m hmi hmj
          rw [h_path_m_eq] at hw_m'
          -- w was shared between l and m in sp, so l was crowded
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨m, hlm, w, by simp [hw_l', hw_m']⟩

  -- Now we can show i is the min of sp'.2.crowdedPathIndices
  have hi'_min : i = sp'.2.crowdedPathIndices.min'
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') := by
    apply le_antisymm
    · apply Finset.le_min'
      intro l hl
      by_contra h
      push Not at h
      exact h_no_smaller_crowded l h hl
    · exact Finset.min'_le sp'.2.crowdedPathIndices i hi'_crowded

  -- v is crowded in sp' (on both paths i and j)
  have hv_crowded' : v ∈ sp'.2.crowdedVerticesOnPath i := by
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hvi', j, hij, hvj'⟩

  -- pathIndicesContaining v is preserved
  have h_pathIndices_eq := signReversing_pathIndicesContaining_eq hac sp hip i j hij v hvi hvj h_data

  -- The final equality requires showing that all components of getCanonicalIntersectionData match:
  -- 1. i is the min of crowdedPathIndices (shown in hi'_min)
  -- 2. The firstCrowdedIndexOnPath gives the same index (v is still first crowded vertex)
  -- 3. The vertex at that index is v (since heads are preserved)
  -- 4. j is the max of (pathIndicesContaining v \ {i}) (by h_pathIndices_eq)

  -- For (2) and (3): The head of path i is preserved by exchangeTails_head_eq,
  -- and the crowded status of vertices before v is preserved (shown in h_no_smaller_crowded analysis).
  -- Since v was the first crowded vertex in sp, it remains the first in sp'.

  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩

  -- The index of v on path i
  let idx := sp.2.firstCrowdedIndexOnPath i
  have h_idx : idx < (sp.2.paths i).vertices.length := sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded

  -- Key fact: v is at index idx on path i
  have h_v_at_idx : (sp.2.paths i).vertices[idx]'h_idx = v := by
    -- By definition of getCanonicalIntersectionData, v is defined as the vertex at firstCrowdedIndexOnPath i
    -- We extract this from h_data
    have h_v_eq : v = (getCanonicalIntersectionData sp.2 hip).val.2.2.val := by
      rw [h_data]
    -- Unfold getCanonicalIntersectionData to see that the result is (paths i').get ⟨idx', h_idx'⟩
    -- where i' = crowdedPathIndices.min' and idx' = firstCrowdedIndexOnPath i'
    simp only [getCanonicalIntersectionData] at h_v_eq
    -- h_v_eq now shows v = (sp.2.paths (min' ...)).vertices.get ⟨firstCrowdedIndexOnPath (min' ...), _⟩
    -- Since i = min' (by hi_min_sp), this gives us what we need
    rw [h_v_eq]
    -- Now need to show (sp.2.paths i).vertices[idx] = (sp.2.paths (min' ...)).vertices.get ...
    -- Use hi_min_sp: i = min' ...
    -- First, rewrite i to min' in the goal
    have h_idx_eq : idx = sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min'
        (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)) := by
      exact congrArg sp.2.firstCrowdedIndexOnPath hi_min_sp
    simp only [hi_min_sp, h_idx_eq, List.get_eq_getElem]

  -- Key fact: idx equals the findIdx of v on path i
  have h_idx_eq_findIdx : idx = (sp.2.paths i).vertices.findIdx (· = v) := by
    -- Since v is at position idx on path i (by h_v_at_idx), and vertices are distinct
    -- (by acyclicity), findIdx (· = v) = idx
    have hnodup := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
    have h_mem : v ∈ (sp.2.paths i).vertices := hvi
    have h_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, h_mem, by simp⟩
    have h_get := @List.findIdx_getElem _ (· = v) (sp.2.paths i).vertices h_lt
    simp only [decide_eq_true_eq] at h_get
    -- h_get : (sp.2.paths i).vertices[findIdx] = v
    -- h_v_at_idx : (sp.2.paths i).vertices[idx] = v
    -- Since vertices are distinct, findIdx = idx
    have h_eq : (sp.2.paths i).vertices[(sp.2.paths i).vertices.findIdx (· = v)]'h_lt =
                (sp.2.paths i).vertices[idx]'h_idx := by
      rw [h_get, h_v_at_idx]
    exact (hnodup.getElem_inj_iff.mp h_eq).symm

  -- Key fact: firstCrowdedIndexOnPath gives the same index in sp' as in sp
  have h_firstCrowded_eq : sp'.2.firstCrowdedIndexOnPath i = idx := by
      -- This follows from:
      -- 1. Vertices before v on path i are not crowded in sp' (by vertices_before_v_not_crowded_in_sp')
      -- 2. v is crowded in sp' (by hv_crowded')
      -- 3. The head of path i is preserved (by exchangeTails_head_eq)

      -- First, show that the head of path i is preserved
      have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
        signReversing_path_i hac sp hip i j hij v hvi hvj h_data

      simp only [PathTuple.firstCrowdedIndexOnPath]

      -- sp'.paths i has vertices = head_p ++ tail_q.tail
      have h_sp'_verts : (sp'.2.paths i).vertices =
          ((sp.2.paths i).splitAt v hvi).1.vertices ++
          ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
        rw [h_path_i_eq, exchangeTails_fst_vertices]

      -- head_p has length idx + 1
      have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
        rw [splitAt_fst_vertices]
        rw [List.length_take]
        have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
        rw [h_idx_eq_findIdx]
        omega

      -- idx < length of sp'.paths i
      have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
        rw [h_sp'_verts, List.length_append]
        have : 0 < ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length ∨
               ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length = 0 := by omega
        rcases this with hpos | hzero
        · omega
        · rw [h_head_len]; omega

      -- The key insight: sp'.paths i has the same first (idx+1) vertices as sp.paths i
      have h_prefix : ∀ m : ℕ, (hm : m ≤ idx) →
          (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') =
          (sp.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx) := by
        intro m hm
        have h_m_lt_head : m < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
          rw [h_head_len]; omega
        have h1 : (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') =
            (((sp.2.paths i).splitAt v hvi).1.vertices ++
             ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[m]'(by
               rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
        rw [h1, List.getElem_append_left h_m_lt_head]
        simp only [splitAt_fst_vertices, List.getElem_take]

      -- The vertex at position idx in sp'.paths i is v
      have h_v_at_idx' : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v :=
        (h_prefix idx (Nat.le_refl idx)).trans h_v_at_idx

      -- v is crowded in sp' (already have hv_crowded')
      have h_v_crowded_bool : (fun w => w ∈ sp'.2.crowdedVerticesOnPath i) v := hv_crowded'

      -- For m < idx, the vertex at position m is not crowded in sp'
      have h_before_not_crowded : ∀ m : ℕ, (hm : m < idx) →
          ¬((sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') ∈ sp'.2.crowdedVerticesOnPath i) := by
        intro m hm
        have h_m_lt_sp : m < (sp.2.paths i).vertices.length := Nat.lt_trans hm h_idx
        have h_getElem_eq : (sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') =
            (sp.2.paths i).vertices[m]'h_m_lt_sp := h_prefix m (Nat.le_of_lt hm)
        rw [h_getElem_eq]
        have h_m_lt_findIdx : m < (sp.2.paths i).vertices.findIdx (· = v) := by
          rw [← h_idx_eq_findIdx]; exact hm
        exact vertices_before_v_not_crowded_in_sp' hac sp hip i j hij v hvi hvj h_data
          ((sp.2.paths i).vertices[m]'h_m_lt_sp) m h_m_lt_findIdx h_m_lt_sp rfl

      -- Apply findIdx_eq_of_first
      exact findIdx_eq_of_first (sp'.2.paths i).vertices
        (fun w => decide (w ∈ sp'.2.crowdedVerticesOnPath i)) idx h_idx_lt'
        (fun m hm => by
          have := h_before_not_crowded m hm
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact this)
        (by simp only [decide_eq_true_eq]; rw [h_v_at_idx']; exact h_v_crowded_bool)

  -- Now we can show getCanonicalIntersectionData returns the same (i, j, v)
  -- The component equalities are established (hi'_min, h_firstCrowded_eq, h_pathIndices_eq)
  -- The final equality follows from these.

  -- First, establish that the min equals i
  have h_min_eq : sp'.2.crowdedPathIndices.min'
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := hi'_min.symm

  -- The vertex at the first crowded index on path i in sp' is v
  -- We need to re-derive h_v_at_idx' here since it was local to h_firstCrowded_eq
  have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices =
        ((sp.2.paths i).splitAt v hvi).1.vertices ++
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    rw [h_sp'_verts, List.length_append, h_head_len]; omega

  have h_v_at_idx'_new : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices =
        ((sp.2.paths i).splitAt v hvi).1.vertices ++
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    have h_idx_lt_head : idx < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
      rw [h_head_len]; omega
    calc (sp'.2.paths i).vertices[idx]'h_idx_lt'
        = (((sp.2.paths i).splitAt v hvi).1.vertices ++
           ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[idx]'(by rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
      _ = ((sp.2.paths i).splitAt v hvi).1.vertices[idx]'h_idx_lt_head := by
          rw [List.getElem_append_left h_idx_lt_head]
      _ = (sp.2.paths i).vertices[idx]'h_idx := by
          simp only [splitAt_fst_vertices, List.getElem_take]
      _ = v := h_v_at_idx

  -- Now show the vertex computed by getCanonicalIntersectionData equals v
  have h_v_eq' : (sp'.2.paths (sp'.2.crowdedPathIndices.min'
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip'))).vertices.get
      ⟨sp'.2.firstCrowdedIndexOnPath (sp'.2.crowdedPathIndices.min'
        (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip')),
       sp'.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
    simp only [h_min_eq, h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new

  -- The max of (pathIndicesContaining v \ {i}) in sp' equals j
  have h_max_eq : ∀ h_sdiff_ne : (sp'.2.pathIndicesContaining v \ {i}).Nonempty,
      (sp'.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne = j := by
    intro h_sdiff_ne
    have h_eq : sp'.2.pathIndicesContaining v \ {i} = sp.2.pathIndicesContaining v \ {i} := by
      rw [h_pathIndices_eq]
    -- j is in the set
    have hj_mem_sp' : j ∈ sp'.2.pathIndicesContaining v \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                 Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hvj', hij.symm⟩
    -- j is maximal: for all k in the set, k ≤ j
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining v \ {i}, k ≤ j := by
      intro k hk
      rw [h_eq] at hk
      -- k is in sp.2.pathIndicesContaining v \ {i}
      -- j is the max' of this set (from h_data)
      -- We use the fact that h_data tells us j = max' of pathIndicesContaining v \ {i}
      have hj_mem_sp : j ∈ sp.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj, hij.symm⟩
      -- From h_data, j is the max' of sp.2.pathIndicesContaining v \ {i}
      -- We need to show k ≤ j
      -- Since both k and j are in the same finite set, and j is the max from h_data
      have h_sdiff_ne_sp : (sp.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, hj_mem_sp⟩
      -- Extract from h_data that j equals the max'
      -- getCanonicalIntersectionData returns j = max' (pathIndicesContaining (vertex at idx) \ {i})
      -- where vertex at idx = v (by h_v_at_idx) and i = min' (by hi_min_sp)
      -- So j = max' (pathIndicesContaining v \ {i})
      have h_j_is_max : j = (sp.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne_sp := by
        -- From the definition of getCanonicalIntersectionData and h_data
        -- The j component equals max' (pathIndicesContaining v \ {i})
        -- This is a consequence of h_data which specifies the exact form
        simp only [getCanonicalIntersectionData] at h_data
        have h := congrArg (fun x => x.val.2.1) h_data
        simp only at h
        rw [← h]
        -- Now we need to show the sets are equal
        -- The vertex in the definition equals v, and min' = i
        have h_vert : (sp.2.paths (sp.2.crowdedPathIndices.min'
            (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))).vertices.get
            ⟨sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min'
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)),
             sp.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
          -- Use hi_min_sp : i = min' ... to rewrite
          have h_eq : sp.2.crowdedPathIndices.min'
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) = i := hi_min_sp.symm
          simp only [h_eq, List.get_eq_getElem]
          exact h_v_at_idx
        simp only [h_vert, hi_min_sp]
      rw [h_j_is_max]
      exact Finset.le_max' _ _ hk
    exact le_antisymm (Finset.max'_le _ h_sdiff_ne j hj_max) (Finset.le_max' _ j hj_mem_sp')

  -- Now construct the equality using Subtype.ext
  -- The goal is to show:
  -- getCanonicalIntersectionData sp'.2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩
  --
  -- We have established:
  -- - h_min_eq: min' crowdedPathIndices = i
  -- - h_firstCrowded_eq: firstCrowdedIndexOnPath i = idx
  -- - h_v_eq': vertex at that index = v
  -- - h_max_eq: max' (pathIndicesContaining v \ {i}) = j
  --
  -- The final equality involves complex dependent type transport.
  -- The key insight is that all components (i, j, v) are the same,
  -- so the equality holds by construction.
  simp only [getCanonicalIntersectionData]
  apply Subtype.ext
  simp only

  -- Use Sigma.ext for the nested sigma types
  have h1 : sp'.2.crowdedPathIndices.min'
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := h_min_eq

  -- Get the vertex at firstCrowdedIndexOnPath i
  have h_vert : (sp'.2.paths i).vertices.get
      ⟨sp'.2.firstCrowdedIndexOnPath i,
       sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩ = v := by
    simp only [h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new

  -- Get the nonemptiness proof
  have h_ne : (sp'.2.pathIndicesContaining
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).Nonempty := by
    have h_mem := sp'.2.firstCrowdedVertex_mem_crowdedVerticesOnPath i
      (by rw [← h1]; exact Finset.min'_mem _ _)
    exact sp'.2.pathIndicesContaining_sdiff_singleton_nonempty i
      (by rw [← h1]; exact Finset.min'_mem _ _) _ h_mem

  -- The j computed by getCanonicalIntersectionData equals j
  have h_j_eq : (sp'.2.pathIndicesContaining
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne = j := by
    -- The vertex equals v, so pathIndicesContaining (vertex) = pathIndicesContaining v
    -- j is in the set and is maximal
    have hj_mem : j ∈ sp'.2.pathIndicesContaining
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert]
      exact ⟨hvj', hij.symm⟩
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}, k ≤ j := by
      intro k hk
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert] at hk
      -- k ∈ pathIndicesContaining v \ {i}
      have hk' : k ∈ sp'.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact hk
      -- j is the max of pathIndicesContaining v \ {i}
      have h_ne' : (sp'.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter,
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj', hij.symm⟩⟩
      have hj_is_max := h_max_eq h_ne'
      rw [← hj_is_max]
      exact Finset.le_max' _ _ hk'
    exact le_antisymm (Finset.max'_le _ h_ne j hj_max) (Finset.le_max' _ j hj_mem)

  -- The equality follows from h1, h_vert, h_j_eq
  -- All components match: i = min', v = vertex at idx, j = max'
  -- The proof involves dependent type transport
  --
  -- The key insight is that:
  -- - i = min' crowdedPathIndices (by h_min_eq = hi'_min.symm)
  -- - v = vertex at firstCrowdedIndexOnPath (by h_vert)
  -- - j = max' (pathIndicesContaining v \ {i}) (by h_j_eq)
  --
  -- After subst h1, the goal becomes showing equality of sigma types
  -- where all components are definitionally equal after the substitution.
  -- The final equality is a technical dependent type manipulation.
  -- All the mathematical content has been verified above.

  -- Use subst to eliminate h1, then use HEq for the remaining components
  -- First, convert the equalities to HEq before subst
  have h_j_heq : HEq
      ((sp'.2.pathIndicesContaining
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne)
      j := heq_of_eq h_j_eq

  -- The vertex subtype needs HEq as well
  have h_vert_heq : HEq
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i,
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩)
      v := heq_of_eq h_vert

  subst h1
  -- Now use cases on the HEq
  cases h_j_heq
  cases h_vert_heq
  rfl

theorem signReversing_involutive {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    let sp' := signReversing hac sp hip
    ∃ hip' : sp'.2.isIntersecting, signReversing hac sp' hip' = sp := by
  -- The proof uses the canonical (deterministic) selection of intersection data.
  -- With getCanonicalIntersectionData, the same (i, j, v) is selected for both sp and sp'.
  --
  -- Key insight: After exchangeTails at (i, j, v):
  -- - The head of path i (vertices before v) is unchanged
  -- - The head of path j (vertices before v) is unchanged
  -- - So crowdedPathIndices is the same, i is still the smallest
  -- - v is still the first crowded vertex on path i
  -- - pathIndicesContaining v is the same, j is still the largest
  --
  -- Once we have the same (i, j, v), the result follows from:
  -- - Permutation: (σ * swap i j) * swap i j = σ (by Equiv.swap_mul_self)
  -- - Paths: exchangeTails(exchangeTails(p_i, p_j, v)) = (p_i, p_j) (by exchangeTails_involutive)
  use signReversing_isIntersecting hac sp hip
  -- Extract the canonical intersection data for sp
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data

  -- Set up sp' and its properties
  set sp' := signReversing hac sp hip with h_sp'
  set hip' := signReversing_isIntersecting hac sp hip with h_hip'

  -- First, let's establish the path equalities we need
  have h_sp'_path_i : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
    signReversing_path_i hac sp hip i j hij v hvi hvj h_data
  have h_sp'_path_j : sp'.2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 :=
    signReversing_path_j hac sp hip i j hij v hvi hvj h_data
  have h_sp'_perm : sp'.1 = sp.1 * Equiv.swap i j :=
    signReversing_perm_eq hac sp hip i j hij v hvi hvj h_data

  -- Use the key invariance lemma
  obtain ⟨hvi', hvj', h_data'⟩ := signReversing_canonical_eq hac sp hip i j hij v hvi hvj h_data hip'

  -- Now we can prove signReversing hac sp' hip' = sp
  -- First show the permutations are equal
  have h_perm_eq : (signReversing hac sp' hip').1 = sp.1 := by
    have h_perm' : (signReversing hac sp' hip').1 = sp'.1 * Equiv.swap i j := by
      conv_lhs => unfold signReversing; rw [h_data']
    rw [h_perm', h_sp'_perm]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]

  -- Show path equality using exchangeTails_involutive
  -- Key: sp'.paths i = exchangeTails(sp.paths i, sp.paths j, v).1
  --      sp'.paths j = exchangeTails(sp.paths i, sp.paths j, v).2
  -- So: (signReversing sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v).1
  --     = exchangeTails(exchangeTails(sp.paths i, sp.paths j, v).1,
  --                     exchangeTails(sp.paths i, sp.paths j, v).2, v).1
  --     = sp.paths i  (by exchangeTails_involutive)

  -- Use exchangeTails_involutive to show the paths are equal to sp's paths
  have h_invol := exchangeTails_involutive hac (sp.2.paths i) (sp.2.paths j) v hvi hvj

  -- Define the intermediate paths for clarity
  set p_i' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 with h_p_i'_def
  set p_j' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 with h_p_j'_def

  -- The membership proofs from exchangeTails
  have hvi_exch : v ∈ p_i'.vertices := exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj_exch : v ∈ p_j'.vertices := exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj

  -- Extract the equalities from h_invol
  have h_invol_fst : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).1 = sp.2.paths i := by
    have := congr_arg Prod.fst h_invol
    simp only at this
    exact this
  have h_invol_snd : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).2 = sp.2.paths j := by
    have := congr_arg Prod.snd h_invol
    simp only at this
    exact this

  -- Key: sp'.paths i = p_i' and sp'.paths j = p_j'
  have h_sp'_i_eq : sp'.2.paths i = p_i' := h_sp'_path_i
  have h_sp'_j_eq : sp'.2.paths j = p_j' := h_sp'_path_j

  -- Cast the membership proofs to the correct types
  have hvi'_cast : v ∈ p_i'.vertices := h_sp'_i_eq ▸ hvi'
  have hvj'_cast : v ∈ p_j'.vertices := h_sp'_j_eq ▸ hvj'

  -- Show path i equality
  have h_path_i_eq : (signReversing hac sp' hip').2.paths i = sp.2.paths i := by
    -- (signReversing hac sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v, hvi', hvj').1
    have h1 : (signReversing hac sp' hip').2.paths i =
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 :=
      signReversing_path_i hac sp' hip' i j hij v hvi' hvj' h_data'
    -- Rewrite using the path equalities
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 =
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).1 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    -- Now use proof irrelevance: hvi'_cast and hvi_exch are both proofs of v ∈ p_i'.vertices
    convert h_invol_fst using 2

  -- Show path j equality
  have h_path_j_eq : (signReversing hac sp' hip').2.paths j = sp.2.paths j := by
    have h1 : (signReversing hac sp' hip').2.paths j =
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 :=
      signReversing_path_j hac sp' hip' i j hij v hvi' hvj' h_data'
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 =
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).2 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    convert h_invol_snd using 2

  -- Show other paths are unchanged
  have h_path_other : ∀ l, l ≠ i → l ≠ j → (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l hl_ne_i hl_ne_j
    have h1 : (signReversing hac sp' hip').2.paths l = sp'.2.paths l :=
      signReversing_path_other hac sp' hip' i j hij v hvi' hvj' h_data' l hl_ne_i hl_ne_j
    have h2 : sp'.2.paths l = sp.2.paths l :=
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_ne_i hl_ne_j
    rw [h1, h2]

  -- Combine to show full equality
  -- We need to show signReversing hac sp' hip' = sp
  -- Both are elements of pathTupleWithPerm A B = (σ : Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)
  -- We have h_perm_eq : (signReversing hac sp' hip').1 = sp.1
  -- And we need to show the PathTuples are equal

  -- First, let's show all paths are equal
  have h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l
    by_cases hl_i : l = i
    · subst hl_i; exact h_path_i_eq
    · by_cases hl_j : l = j
      · subst hl_j; exact h_path_j_eq
      · exact h_path_other l hl_i hl_j

  -- Use Sigma.ext with the permutation equality
  -- The key is that h_perm_eq shows the first components are equal
  -- We need HEq for the second components
  -- Since the first components are equal, the types are equal, so HEq reduces to Eq
  have h_type_eq : PathTuple D k A (permuteKVertex (signReversing hac sp' hip').1 B) =
                   PathTuple D k A (permuteKVertex sp.1 B) := by
    congr 1
    exact congrArg (permuteKVertex · B) h_perm_eq

  -- Now we can use the type equality to cast
  -- The key insight is that we need to show HEq between the PathTuples
  -- Since the permutations are equal, the target types are equal

  -- Direct approach: construct the equality using cases
  cases sp with
  | mk σ pt =>
    simp only at h_perm_eq h_paths_eq ⊢
    -- h_perm_eq : (signReversing hac sp' hip').1 = σ
    -- h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = pt.paths l
    -- Goal: signReversing hac sp' hip' = ⟨σ, pt⟩

    -- Destruct the signReversing result
    set sr := signReversing hac sp' hip' with h_sr_def
    obtain ⟨sr_perm, sr_pt⟩ := sr
    simp only at h_perm_eq h_paths_eq
    -- h_perm_eq : sr_perm = σ
    -- h_paths_eq : ∀ l, sr_pt.paths l = pt.paths l

    -- Subst the permutation equality
    subst h_perm_eq
    -- Now sr_pt and pt have the same type
    -- Goal: ⟨σ, sr_pt⟩ = ⟨σ, pt⟩
    congr 1
    -- Goal: sr_pt = pt
    ext l
    exact h_paths_eq l


/-- The permutation of signReversing is the original permutation composed with a transposition.
    This captures the essential structural property of the sign-reversing involution:
    when we exchange tails at indices i and j, we compose σ with the transposition (i j). -/
theorem signReversing_perm {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧ (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  -- By definition of signReversing, the permutation component is sp.1 * Equiv.swap i j
  -- where (i, j, v) are extracted by getCanonicalIntersectionData
  unfold signReversing
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  exact ⟨i, j, hij, rfl⟩

/-- The paths of signReversing are obtained by exchanging tails at indices i and j.
    This captures the essential structural property of the sign-reversing involution
    for the paths: paths at indices i and j have their tails exchanged at the crowded
    point v, while all other paths remain unchanged. -/
theorem signReversing_paths {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧
      ∃ v : V, ∃ hvi : v ∈ (sp.2.paths i).vertices, ∃ hvj : v ∈ (sp.2.paths j).vertices,
        (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 ∧
        (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 ∧
          ∀ l, l ≠ i → l ≠ j → (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  -- signReversing uses getCanonicalIntersectionData to get (i, j, v, hvi, hvj)
  -- Since getCanonicalIntersectionData is deterministic, the same call returns the same value
  -- We use generalize to ensure we're working with the same data
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Now signReversing uses h_data to get the same (i, j, v, hvi, hvj)
  refine ⟨i, j, hij, v, hvi, hvj, ?_, ?_, ?_⟩
  · -- Path i is the first component of exchangeTails
    show (signReversing hac sp hip).2.paths i = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
  · -- Path j is the second component of exchangeTails
    show (signReversing hac sp hip).2.paths j = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
  · -- Other paths are unchanged
    intro l hl_ne_i hl_ne_j
    show (signReversing hac sp hip).2.paths l = sp.2.paths l
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- The sign-reversing map flips the sign -/
theorem signReversing_sign {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signOfPathTupleWithPerm (signReversing hac sp hip) = -signOfPathTupleWithPerm sp := by
  -- The sign-reversing map composes the permutation with a transposition (i j)
  -- Since sign(σ * swap i j) = sign(σ) * sign(swap i j) = sign(σ) * (-1) = -sign(σ)
  obtain ⟨i, j, hij, heq⟩ := signReversing_perm hac sp hip
  unfold signOfPathTupleWithPerm
  rw [heq, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  exact mul_neg_one (Equiv.Perm.sign sp.1)

/-- The sign-reversing map preserves weight -/
theorem signReversing_weight {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K)
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    weightOfPathTupleWithPerm w (signReversing hac sp hip) = weightOfPathTupleWithPerm w sp := by
  -- The sign-reversing map exchanges tails of paths at indices i and j
  -- All other paths remain unchanged
  -- The product of weights is preserved because:
  --   w(p_i) * w(p_j) = w(p'_i) * w(p'_j) (by exchangeTails_weight)
  --   and all other w(p_k) are unchanged
  obtain ⟨i, j, hij, v, hvi, hvj, hi_eq, hj_eq, h_rest⟩ := signReversing_paths hac sp hip
  unfold weightOfPathTupleWithPerm pathTupleWeight
  -- Show the product at indices i and j is preserved
  have h_ij : pathWeight w ((signReversing hac sp hip).2.paths i) *
              pathWeight w ((signReversing hac sp hip).2.paths j) =
              pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) := by
    rw [hi_eq, hj_eq]
    exact (exchangeTails_weight w (sp.2.paths i) (sp.2.paths j) v hvi hvj).symm
  -- Factor the products
  have h1 : ∏ l, pathWeight w ((signReversing hac sp hip).2.paths l) =
            pathWeight w ((signReversing hac sp hip).2.paths i) *
            pathWeight w ((signReversing hac sp hip).2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  have h2 : ∏ l, pathWeight w (sp.2.paths l) =
            pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  -- Show the rest of the product is unchanged
  have h3 : ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) =
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [Finset.mem_erase] at hl
    rw [h_rest l hl.2.1 hl.1]
  rw [h1, h2, h_ij, h3]

/-- The sign-reversing map has no fixed points (since it always flips the sign) -/
theorem signReversing_no_fixed_points {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signReversing hac sp hip ≠ sp := by
  intro heq
  have hsign := signReversing_sign hac sp hip
  rw [heq] at hsign
  simp at hsign

/-!
## Infrastructure for LGV Proof

The following definitions and lemmas provide the infrastructure needed to complete
the LGV theorem proof. The key steps are:
1. Define the finset of all path tuples
2. Define the finset of intersecting path tuples (ipats)
3. Prove that the signed sum over ipats is 0 using the sign-reversing involution
-/

/-- The set of all path tuples from A to B -/
def allPathTupleSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  Set.univ

/-- The set of all path tuples is finite (follows from path-finiteness) -/
noncomputable def allPathTupleSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Set.Finite (allPathTupleSet (D := D) A B) := by
  -- The proof is essentially the same as nipatSetFinite
  let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i =>
    {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
  have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
  have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) :=
    Set.Finite.pi (fun i => h_each_finite i)
  let f : (allPathTupleSet (D := D) A B) → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
    ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
  have hf_inj : Function.Injective f := by
    intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
    simp only [Subtype.mk.injEq, f] at heq ⊢
    cases pt1; cases pt2
    simp only [PathTuple.mk.injEq] at heq ⊢
    exact heq
  have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
  have h_finite : Finite (allPathTupleSet (D := D) A B) := Finite.of_injective f hf_inj
  exact Set.finite_coe_iff.mp h_finite

/-- Convert allPathTupleSet to Finset -/
noncomputable def allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (allPathTupleSetFinite hpf A B).toFinset

/-- Every path tuple is in allPathTupleFinset -/
theorem mem_allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ allPathTupleFinset hpf A B := by
  simp only [allPathTupleFinset, Set.Finite.mem_toFinset, allPathTupleSet, Set.mem_univ]

/-- The set of intersecting path tuples (ipats) -/
def ipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isIntersecting}

/-- The set of ipats is finite -/
noncomputable def ipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (ipatSet (D := D) A B) :=
  (allPathTupleSetFinite hpf A B).subset (fun _ _ => trivial)

/-- Convert ipatSet to Finset -/
noncomputable def ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (ipatSetFinite hpf A B).toFinset

/-- Membership in ipatFinset -/
theorem mem_ipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ ipatFinset hpf A B ↔ pt.isIntersecting := by
  simp only [ipatFinset, Set.Finite.mem_toFinset, ipatSet, Set.mem_setOf_eq]

/-- Membership in nipatFinset -/
theorem mem_nipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ nipatFinset hpf A B ↔ pt.isNonIntersecting := by
  simp only [nipatFinset, Set.Finite.mem_toFinset, nipatSet, Set.mem_setOf_eq]

/-- nipats and ipats are disjoint -/
theorem nipatFinset_disjoint_ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatFinset hpf A B) (ipatFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro pt1 h1 pt2 h2 heq
  rw [mem_nipatFinset_iff] at h1
  rw [mem_ipatFinset_iff] at h2
  subst heq
  -- h1 : pt1.isNonIntersecting, h2 : pt1.isIntersecting
  -- isIntersecting = ¬isNonIntersecting, so we have a contradiction
  exact h2 h1

/-- nipats ∪ ipats = all path tuples (set-level equality) -/
theorem nipatFinset_union_ipatFinset_eq {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    ∀ pt, pt ∈ nipatFinset hpf A B ∨ pt ∈ ipatFinset hpf A B ↔
          pt ∈ allPathTupleFinset hpf A B := by
  intro pt
  simp only [mem_nipatFinset_iff, mem_ipatFinset_iff, mem_allPathTupleFinset]
  constructor
  · intro _; trivial
  · intro _
    -- isIntersecting = ¬isNonIntersecting, so exactly one holds
    by_cases h : pt.isNonIntersecting
    · exact Or.inl h
    · exact Or.inr h

/-- The product of path weights equals the sum over path tuples -/
theorem prod_pathWeightSum_eq_sum_pathTupleWeight {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    ∏ j, pathWeightSum hpf w (A j) (B j) =
    ∑ pt ∈ allPathTupleFinset hpf A B, pathTupleWeight w pt.paths := by
  -- Use prod_univ_sum to expand the product
  simp only [pathWeightSum]
  rw [Finset.prod_univ_sum]
  -- Establish bijection between piFinset and allPathTupleFinset
  refine Finset.sum_bij'
    -- forward: function → PathTuple
    (fun g hg => PathTuple.mk g
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset,
                   Set.mem_setOf_eq] at hg
        exact (hg j).1)
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset,
                   Set.mem_setOf_eq] at hg
        exact (hg j).2))
    -- backward: PathTuple → function
    (fun pt _ => pt.paths)
    -- hi: forward maps into allPathTupleFinset
    (fun g hg => mem_allPathTupleFinset hpf _)
    -- hj: backward maps into piFinset
    (fun pt hpt => by
      simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro j
      exact ⟨pt.starts j, pt.finishes j⟩)
    -- left_inv: j(i(g)) = g
    (fun g hg => rfl)
    -- right_inv: i(j(pt)) = pt
    (fun pt hpt => by cases pt; rfl)
    -- function equality
    (fun g hg => rfl)

/-- The set of all intersecting path tuples with permutation.
    This is the domain of the sign-reversing involution. -/
def ipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isIntersecting}

/-- PathTuple is finite when the digraph is path-finite. -/
theorem pathTupleFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Finite (PathTuple D k A B) := by
  have h := allPathTupleSetFinite hpf A B
  -- allPathTupleSet A B = Set.univ, so h : Set.Finite Set.univ
  -- We need to convert this to Finite (PathTuple D k A B)
  rw [allPathTupleSet] at h
  exact Set.finite_univ_iff.mp h

/-- pathTupleWithPerm is finite when the digraph is path-finite. -/
theorem pathTupleWithPermFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Finite (pathTupleWithPerm (D := D) A B) := by
  unfold pathTupleWithPerm
  have h_perm_finite : Finite (Equiv.Perm (Fin k)) := inferInstance
  have h_pt_finite : ∀ σ : Equiv.Perm (Fin k),
      Finite (PathTuple D k A (permuteKVertex σ B)) := by
    intro σ
    exact pathTupleFinite hpf A (permuteKVertex σ B)
  exact inferInstance

/-- The set of intersecting path tuples with permutation is finite. -/
noncomputable def ipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Set.Finite (ipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert ipatWithPermSet to Finset -/
noncomputable def ipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Finset (pathTupleWithPerm (D := D) A B) :=
  (ipatWithPermSetFinite hpf A B).toFinset

/-- Membership in ipatWithPermFinset -/
theorem mem_ipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ ipatWithPermFinset hpf A B ↔ sp.2.isIntersecting := by
  simp only [ipatWithPermFinset, Set.Finite.mem_toFinset, ipatWithPermSet, Set.mem_setOf_eq]

/-- The signed sum over ALL intersecting path tuples (with permutation) is zero.

    This is the correct formulation of the cancellation lemma. The sign-reversing
    involution `signReversing` maps (σ, pt) to (σ * swap i j, pt'), where:
    - sign(σ * swap i j) = -sign(σ)  (sign flips)
    - weight(pt') = weight(pt)       (weight preserved)

    So each pair {sp, signReversing(sp)} contributes:
      sign(σ) * w(pt) + sign(σ * swap i j) * w(pt')
    = sign(σ) * w(pt) + (-sign(σ)) * w(pt)
    = 0

    The total sum is therefore 0.

    Note: This works in any CommRing K, including characteristic 2, because we're
    summing pairs that each contribute 0, not just showing 2x = 0. -/
theorem sum_ipatWithPerm_signed_weight_eq_zero {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ} (w : ArcWeight D K)
    (A B : kVertex V k) :
    ∑ sp ∈ ipatWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths = 0 := by
  -- The proof uses signReversing as a fixed-point-free involution that:
  -- 1. Maps ipatWithPermFinset to itself (signReversing_isIntersecting)
  -- 2. Flips the sign (signReversing_sign)
  -- 3. Preserves the weight (signReversing_weight)
  -- 4. Has no fixed points (signReversing_no_fixed_points)
  -- 5. Is an involution (signReversing_involutive)
  --
  -- We use Finset.sum_involution to show the sum is 0.
  apply Finset.sum_involution
    (fun sp hsp => signReversing hac sp ((mem_ipatWithPermFinset_iff hpf sp).mp hsp))
  case hg₁ =>
    -- Show: f(sp) + f(g(sp)) = 0
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    -- signReversing flips the sign and preserves the weight
    have hsign := signReversing_sign hac sp hip
    have hweight := signReversing_weight hac w sp hip
    simp only [signOfPathTupleWithPerm] at hsign
    simp only [weightOfPathTupleWithPerm] at hweight
    rw [hsign, hweight]
    simp only [Units.val_neg, Int.cast_neg]
    ring
  case hg₃ =>
    -- Show: f(sp) ≠ 0 → g(sp) ≠ sp (no fixed points)
    intro sp hsp _
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact signReversing_no_fixed_points hac sp hip
  case g_mem =>
    -- Show: g(sp) ∈ s (signReversing preserves membership)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    rw [mem_ipatWithPermFinset_iff]
    exact signReversing_isIntersecting hac sp hip
  case hg₄ =>
    -- Show: g(g(sp)) = sp (involution)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact (signReversing_involutive hac sp hip).choose_spec

/-- The set of all path tuples with permutation -/
def allPathTupleWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  Set.univ

/-- The set of all path tuples with permutation is finite -/
noncomputable def allPathTupleWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Set.Finite (allPathTupleWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ

/-- Convert allPathTupleWithPermSet to Finset -/
noncomputable def allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Finset (pathTupleWithPerm (D := D) A B) :=
  (allPathTupleWithPermSetFinite hpf A B).toFinset

/-- Every path tuple with permutation is in allPathTupleWithPermFinset -/
theorem mem_allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ allPathTupleWithPermFinset hpf A B := by
  simp only [allPathTupleWithPermFinset, Set.Finite.mem_toFinset, allPathTupleWithPermSet,
             Set.mem_univ]

/-- The set of non-intersecting path tuples with permutation -/
def nipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isNonIntersecting}

/-- The set of non-intersecting path tuples with permutation is finite -/
noncomputable def nipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Set.Finite (nipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert nipatWithPermSet to Finset -/
noncomputable def nipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Finset (pathTupleWithPerm (D := D) A B) :=
  (nipatWithPermSetFinite hpf A B).toFinset

/-- Membership in nipatWithPermFinset -/
theorem mem_nipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ nipatWithPermFinset hpf A B ↔ sp.2.isNonIntersecting := by
  simp only [nipatWithPermFinset, Set.Finite.mem_toFinset, nipatWithPermSet, Set.mem_setOf_eq]

/-- nipats and ipats with permutation are disjoint -/
theorem nipatWithPermFinset_disjoint_ipatWithPermFinset {V : Type*} [DecidableEq V]
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatWithPermFinset hpf A B) (ipatWithPermFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro sp1 h1 sp2 h2 heq
  rw [mem_nipatWithPermFinset_iff] at h1
  rw [mem_ipatWithPermFinset_iff] at h2
  subst heq
  exact h2 h1

/-- nipats ∪ ipats with permutation = all path tuples with permutation (as a sum equality) -/
theorem nipatWithPermFinset_union_ipatWithPermFinset_sum {V : Type*} [DecidableEq V]
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k)
    (f : pathTupleWithPerm (D := D) A B → K) :
    ∑ sp ∈ nipatWithPermFinset hpf A B, f sp + ∑ sp ∈ ipatWithPermFinset hpf A B, f sp =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, f sp := by
  symm
  have hdec : DecidablePred (fun sp : pathTupleWithPerm (D := D) A B => sp.2.isNonIntersecting) := by
    intro sp
    exact Classical.dec _
  rw [← Finset.sum_filter_add_sum_filter_not (s := allPathTupleWithPermFinset hpf A B)
      (p := fun sp => sp.2.isNonIntersecting)]
  congr 1
  · -- Show: filter for nipats = nipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and,
                 mem_nipatWithPermFinset_iff]
    · intro _ _; rfl
  · -- Show: filter for ipats = ipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and,
                 mem_ipatWithPermFinset_iff]
      rfl
    · intro _ _; rfl

/-- The sum over all path tuples with permutation splits into nipats and ipats -/
theorem sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat {V : Type*} [DecidableEq V]
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K)
    (A B : kVertex V k) :
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ sp ∈ nipatWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths +
    ∑ sp ∈ ipatWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  rw [← nipatWithPermFinset_union_ipatWithPermFinset_sum hpf A B]

/-- The sum over nipats with permutation equals the sum over permutations of nipatWeightSum -/
theorem sum_nipatWithPerm_eq_sum_nipatWeightSum {V : Type*} [DecidableEq V]
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K)
    (A B : kVertex V k) :
    ∑ sp ∈ nipatWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1: Show nipatWithPermFinset = univ.sigma (fun σ => nipatFinset A (σB))
  have h_eq : nipatWithPermFinset hpf A B =
      Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)) := by
    ext sp
    constructor
    · intro h
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, (mem_nipatWithPermFinset_iff hpf sp).mp h |>
            (mem_nipatFinset_iff hpf _).mpr⟩
    · intro h
      rw [Finset.mem_sigma] at h
      exact (mem_nipatWithPermFinset_iff hpf sp).mpr ((mem_nipatFinset_iff hpf _).mp h.2)
  -- Step 2: Rewrite using sigma sum and factor out sign(σ)
  rw [h_eq]
  calc ∑ sp ∈ Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)),
        (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
      = ∑ σ : Equiv.Perm (Fin k), ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B),
          (Equiv.Perm.sign σ : K) * pathTupleWeight w pt.paths := Finset.sum_sigma _ _ _
    _ = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : K) *
          ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B), pathTupleWeight w pt.paths := by
        apply Finset.sum_congr rfl
        intro σ _
        exact (Finset.mul_sum _ _ _).symm
    _ = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
          nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [nipatWeightSum, Units.smul_def, zsmul_eq_mul]

/-- The determinant can be written as a sum over all path tuples with permutation -/
theorem det_eq_sum_allPathTupleWithPerm {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B,
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  -- Step 1-2: Reindex the determinant using Leibniz formula
  -- det(M) = ∑_σ sign(σ) ∏_i M_{σ(i), i} → ∑_τ sign(τ) ∏_j M_{j, τ(j)}
  rw [Matrix.det_apply']
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _
      (fun τ => (Equiv.Perm.sign τ : K) * ∏ j, (pathWeightMatrix hpf w A B) j (τ j))]
  · -- Step 3: Each product ∏_j M_{j, τ(j)} = ∑_{pt : A → τB} w(pt)
    -- Note: M j (τ j) = pathWeightSum (A j) (B (τ j)) = pathWeightSum (A j) ((permuteKVertex τ B) j)
    have hprod : ∀ τ : Equiv.Perm (Fin k),
        ∏ j, (pathWeightMatrix hpf w A B) j (τ j) =
        ∑ pt ∈ allPathTupleFinset hpf A (permuteKVertex τ B), pathTupleWeight w pt.paths := by
      intro τ
      have heq : ∏ j, (pathWeightMatrix hpf w A B) j (τ j) =
          ∏ j, pathWeightSum hpf w (A j) ((permuteKVertex τ B) j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [pathWeightMatrix, Matrix.of_apply, permuteKVertex]
      rw [heq, prod_pathWeightSum_eq_sum_pathTupleWeight hpf w A (permuteKVertex τ B)]
    simp_rw [hprod]
    -- Now we have: ∑_τ sign(τ) * ∑_{pt ∈ allPathTupleFinset A (τB)} w(pt)
    -- Step 4: Show allPathTupleWithPermFinset = univ.sigma allPathTupleFinset
    have hS : allPathTupleWithPermFinset hpf A B =
        Finset.univ.sigma (fun σ => allPathTupleFinset hpf A (permuteKVertex σ B)) := by
      ext ⟨σ, pt⟩
      constructor
      · intro _
        rw [Finset.mem_sigma]
        exact ⟨Finset.mem_univ σ, mem_allPathTupleFinset hpf pt⟩
      · intro _
        exact mem_allPathTupleWithPermFinset hpf ⟨σ, pt⟩
    rw [hS]
    -- Step 5: Use sum_sigma to combine
    let f : (Σ σ : Equiv.Perm (Fin k), PathTuple D k A (permuteKVertex σ B)) → K :=
      fun sp => (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
    show ∑ τ, _ = ∑ sp ∈ Finset.univ.sigma _, f sp
    rw [Finset.sum_sigma]
    congr 1
    ext τ
    simp only [f]
    rw [Finset.mul_sum]
  · -- Prove the reindexing equality
    intro τ
    simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
    congr 1
    rw [← Equiv.prod_comp τ⁻¹]
    congr 1
    ext i
    simp



/-- LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
    Label: thm.lgv.kpaths.wt-dg

    For any path-finite acyclic digraph D with arc weights w ∈ K:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)

    This generalizes the lattice version - we only use that D is path-finite and acyclic.

    **Proof outline:**
    1. By Leibniz formula: det(M) = ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
    2. Each M_{i,σ(i)} = ∑_{p : A_i → B_{σ(i)}} w(p), so the product expands to
       ∑_{𝐩 : path tuple from 𝐀 to σ(𝐁)} w(𝐩)
    3. Thus det(M) = ∑_σ (-1)^σ ∑_{𝐩 : 𝐀 → σ(𝐁)} w(𝐩)
    4. Split the inner sum into nipats and ipats
    5. The sign-reversing involution on ipats shows ∑_{ipats} (-1)^σ w(𝐩) = 0
    6. Only nipats remain: det(M) = ∑_σ (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩) -/
theorem lgv_weighted_digraph {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ}
    (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1-3: Write determinant as sum over all (σ, pt) pairs
  rw [det_eq_sum_allPathTupleWithPerm hpf w A B]
  -- Step 4: Split into nipats and ipats
  rw [sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat hpf w A B]
  -- Step 5: The ipat sum is 0 by sign-reversing involution
  rw [sum_ipatWithPerm_signed_weight_eq_zero hpf hac w A B, add_zero]
  -- Step 6: The nipat sum equals the RHS
  exact sum_nipatWithPerm_eq_sum_nipatWeightSum hpf w A B

/-- The finite acyclic case obtains path-finiteness from the proved common lemma. -/
theorem lgv_finite [Fintype V] {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix (finite_acyclic_path_finite hac) w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum (finite_acyclic_path_finite hac) w A (permuteKVertex σ B) σ :=
  lgv_weighted_digraph (finite_acyclic_path_finite hac) hac w A B


end DesignExamples.LGV
