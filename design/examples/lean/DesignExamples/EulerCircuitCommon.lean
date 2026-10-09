import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib

set_option backward.isDefEq.respectTransparency false

namespace DesignExamples.EulerCircuit

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable local instance residualDecidable (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

omit [DecidableEq V] in
/-- Maximality is only among trails beginning at the specified vertex. -/
theorem maximal_trail (s : V) :
    ∃ t, ∃ p : G.Walk s t, p.IsTrail ∧
      ∀ z (q : G.Walk s z), q.IsTrail → q.length ≤ p.length := by
  classical
  let lengths : Set ℕ := {n | ∃ t, ∃ p : G.Walk s t, p.IsTrail ∧ p.length = n}
  have hf : lengths.Finite := (Set.finite_le_nat G.edgeFinset.card).subset
    (by rintro n ⟨t, p, hp, rfl⟩; exact hp.length_le_card_edgeFinset)
  obtain ⟨n, ⟨⟨t, p, hp, hlen⟩, hmax⟩⟩ :=
    hf.exists_maximal ⟨0, ⟨s, .nil, by simp⟩⟩
  refine ⟨t, p, hp, ?_⟩
  intro z q hq
  have := hmax ⟨z, q, hq, rfl⟩
  omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- A maximal trail has used every edge incident to its last vertex. -/
theorem maximal_endpoint {s t : V} {p : G.Walk s t} (hp : p.IsTrail)
    (hmax : ∀ z (q : G.Walk s z), q.IsTrail → q.length ≤ p.length)
    {z : V} (hz : G.Adj t z) : s(t, z) ∈ p.edges := by
  classical
  by_contra he
  have hq : (p.concat hz).IsTrail := by
    rw [concat_eq_append, isTrail_append]
    refine ⟨hp, by simp, ?_⟩
    simp [he]
  have := hmax z (p.concat hz) hq
  simp only [length_concat] at this
  omega

/-- The parity of incident edges forces a maximal trail in an even graph to close. -/
theorem closed_trail (even_degree : ∀ v, Even (G.degree v)) (s : V) :
    ∃ p : G.Walk s s, p.IsTrail ∧
      ∀ z (q : G.Walk s z), q.IsTrail → q.length ≤ p.length := by
  classical
  obtain ⟨t, p, hp, hmax⟩ := maximal_trail (G := G) s
  have hinc : G.incidenceFinset t = hp.edgesFinset.filter (t ∈ ·) := by
    ext e
    rw [G.mem_incidenceFinset t, Finset.mem_filter]
    constructor
    · rintro ⟨he, ht⟩
      obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp ht
      exact ⟨maximal_endpoint hp hmax (by simpa using he), by simp⟩
    · rintro ⟨he, ht⟩
      exact ⟨p.edges_subset_edgeSet he, ht⟩
  have hcount : (p.edges.countP fun e => t ∈ e) = G.degree t := by
    rw [← G.card_incidenceFinset_eq_degree, hinc, ← Multiset.coe_countP,
      Multiset.countP_eq_card_filter]
    rfl
  have ht : s = t := by
    by_contra hst
    have := (hp.even_countP_edges_iff t).mp (hcount ▸ even_degree t) hst
    exact this.2 rfl
  subst t
  exact ⟨p, hp, hmax⟩

/-- Removing the edges of a closed trail leaves every degree even. -/
theorem residual_even {s : V} {p : G.Walk s s} (hp : p.IsTrail)
    (even_degree : ∀ v, Even (G.degree v)) :
    ∀ v, Even ((G.deleteEdges p.edgeSet).degree v) := by
  classical
  intro v
  let used := hp.edgesFinset.filter (v ∈ ·)
  have hsub : used ⊆ G.incidenceFinset v := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨he, hv⟩
    exact (G.mem_incidenceFinset v e).mpr ⟨p.edges_subset_edgeSet he, hv⟩
  have hres : (G.deleteEdges p.edgeSet).incidenceFinset v = G.incidenceFinset v \ used := by
    ext e
    simp only [mem_incidenceFinset, incidenceSet, Set.mem_setOf_eq, edgeSet_deleteEdges, Set.mem_sdiff,
      Finset.mem_sdiff, Finset.mem_filter, used]
    change ((e ∈ G.edgeSet ∧ e ∉ p.edges) ∧ v ∈ e) ↔
      (e ∈ G.edgeSet ∧ v ∈ e) ∧ ¬(e ∈ p.edges ∧ v ∈ e)
    tauto
  have hu : Even used.card := by
    have h := (hp.even_countP_edges_iff v).mpr (by simp)
    rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter] at h
    exact h
  have hEven : Even (G.incidenceFinset v \ used).card := by
    rw [Finset.card_sdiff_of_subset hsub, G.card_incidenceFinset_eq_degree]
    have hle : used.card ≤ G.degree v :=
      (Finset.card_le_card hsub).trans_eq (G.card_incidenceFinset_eq_degree v)
    apply (Nat.even_sub' hle).mpr
    constructor
    · intro ho
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) (even_degree v))
    · intro ho
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) hu)
  have hEvenRes : Even ((G.deleteEdges p.edgeSet).incidenceFinset v).card :=
    hres.symm ▸ hEven
  convert hEvenRes using 1
  simp only [SimpleGraph.incidenceFinset, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]
  simpa only [← Nat.card_eq_fintype_card] using
    (Fintype.card_congr ((G.deleteEdges p.edgeSet).incidenceSetEquivNeighborSet v)).symm


/-- An unused edge in the connected component of the current trail gives an insertion vertex. -/
theorem unused_boundary {s : V} (p : G.Walk s s)
    (reach : ∀ v, 0 < G.degree v → G.Reachable s v)
    (hnot : ¬p.IsEulerian) (hp : p.IsTrail) :
    ∃ v, v ∈ p.support ∧ ∃ w, G.Adj v w ∧ s(v, w) ∉ p.edges := by
  classical
  by_contra hn
  push Not at hn
  have used : ∀ v ∈ p.support, ∀ w, G.Adj v w → s(v, w) ∈ p.edges := by
    intro v hv w hw
    exact hn v hv w hw
  have closed : ∀ {u v}, (q : G.Walk u v) → u ∈ p.support → v ∈ p.support := by
    intro u v q
    induction q with
    | nil => exact id
    | @cons u v w huv q ih =>
      intro hu
      exact ih (p.snd_mem_support_of_mem_edges (used u hu v huv))
  apply hnot
  apply hp.isEulerian_of_forall_mem
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : G.Adj u v := by simpa using he
    obtain ⟨q⟩ := reach u huv.degree_pos_left
    exact used u (closed q (by simp)) v huv

/-- A certificate exposes the two walks on either side of an insertion vertex. -/
def InsertionSite {s : V} (p : G.Walk s s) : Prop :=
  ∃ v, ∃ pre : G.Walk s v, ∃ post : G.Walk v s,
    pre.append post = p ∧ ∃ w, G.Adj v w ∧ s(v, w) ∉ p.edges

theorem insertion_site {s : V} (p : G.Walk s s)
    (reach : ∀ v, 0 < G.degree v → G.Reachable s v)
    (hnot : ¬p.IsEulerian) (hp : p.IsTrail) : InsertionSite p := by
  obtain ⟨v, hv, w, hw, he⟩ := unused_boundary p reach hnot hp
  exact ⟨v, p.takeUntil v hv, p.dropUntil v hv, take_spec p hv, w, hw, he⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The splice uses no old edge twice, because the inserted trail uses only residual edges. -/
theorem splice_trail {s v : V} {p : G.Walk s s} (hp : p.IsTrail)
    (pre : G.Walk s v) (post : G.Walk v s) (hsplit : pre.append post = p)
    (q : (G.deleteEdges p.edgeSet).Walk v v) (hq : q.IsTrail) :
    ((pre.append (q.mapLe (G.deleteEdges_le p.edgeSet))).append post).IsTrail := by
  classical
  have hparts := (isTrail_append pre post).mp (hsplit ▸ hp)
  let r := q.mapLe (G.deleteEdges_le p.edgeSet)
  have hdisj : p.edges.Disjoint r.edges := by
    rw [List.disjoint_left]
    intro e he hr
    rw [edges_mapLe_eq_edges] at hr
    exact ((edgeSet_deleteEdges .. ▸ q.edges_subset_edgeSet hr).2) he
  have hdisjPre : pre.edges.Disjoint r.edges := by
    intro e he hr
    apply hdisj _ hr
    rw [← hsplit, edges_append]
    exact List.mem_append_left _ he
  have hdisjPost : post.edges.Disjoint r.edges := by
    intro e he hr
    apply hdisj _ hr
    rw [← hsplit, edges_append]
    exact List.mem_append_right _ he
  rw [isTrail_append]
  refine ⟨(isTrail_append pre r).mpr ⟨hparts.1, hq.mapLe _, hdisjPre⟩, hparts.2.1, ?_⟩
  rw [edges_append, List.disjoint_append_left]
  exact ⟨hparts.2.2, hdisjPost.symm⟩

end DesignExamples.EulerCircuit
