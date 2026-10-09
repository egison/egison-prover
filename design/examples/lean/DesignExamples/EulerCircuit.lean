import DesignExamples.EulerCircuitCommon

set_option backward.isDefEq.respectTransparency false

namespace DesignExamples.EulerCircuit

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem euler_circuit (s : V) (even_degree : ∀ v, Even (G.degree v))
    (reach : ∀ v, 0 < G.degree v → G.Reachable s v) :
    ∃ p : G.Walk s s, p.IsEulerian := by
  classical
  obtain ⟨p, hp, hmax⟩ := closed_trail (G := G) even_degree s
  refine ⟨p, ?_⟩
  by_contra hnot
  obtain ⟨v, hv, w, hw, he⟩ := unused_boundary p reach hnot hp
  let pre := p.takeUntil v hv
  let post := p.dropUntil v hv
  have hsplit : pre.append post = p := take_spec p hv
  let H := G.deleteEdges p.edgeSet
  have heven : ∀ x, Even (H.degree x) := by
    simpa only [H, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card] using residual_even hp even_degree
  obtain ⟨q, hq, hqmax⟩ := closed_trail (G := H) heven v
  have hadj : H.Adj v w := deleteEdges_adj.mpr ⟨hw, he⟩
  have hpositive : 0 < q.length := by
    have := hqmax w hadj.toWalk (by simp)
    simp only [length_cons, length_nil] at this
    omega
  have hlong := hmax s ((pre.append (q.mapLe (G.deleteEdges_le p.edgeSet))).append post)
    (splice_trail hp pre post hsplit q hq)
  have hlen : pre.length + post.length = p.length := by
    rw [← length_append, hsplit]
  simp only [length_append, length_map] at hlong
  omega

/-- Euler's criterion from a specified start, allowing isolated vertices and no edges. -/
theorem euler_circuit_iff (s : V) :
    (∃ p : G.Walk s s, p.IsEulerian) ↔
      (∀ v, Even (G.degree v)) ∧ (∀ v, 0 < G.degree v → G.Reachable s v) := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨fun v => hp.even_degree_iff.mpr (by simp), ?_⟩
    intro v hv
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
    have he : s(v, w) ∈ p.edges := hp.mem_edges_iff.mpr (by simpa using hw)
    exact (p.takeUntil v (p.fst_mem_support_of_mem_edges he)).reachable
  · rintro ⟨heven, hreach⟩
    exact euler_circuit s heven hreach

theorem connected_euler_circuit_iff (connected : G.Connected) (s : V) :
    (∃ p : G.Walk s s, p.IsEulerian) ↔ ∀ v, Even (G.degree v) := by
  rw [euler_circuit_iff]
  exact and_iff_left (fun v _ => connected.preconnected s v)

end DesignExamples.EulerCircuit
