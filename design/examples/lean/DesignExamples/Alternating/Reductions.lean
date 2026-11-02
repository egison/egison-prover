import DesignExamples.Alternating.Coverage

/-! The same commutator constructions are supplied to both proof styles. -/

namespace DesignExamples.Alternating

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem cycle5_path {a b c d e : α} (h : [a, b, c, d, e].Nodup) :
    Path4 (cycle5 a b c d e) a b c d := by
  simp only [Path4, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, not_or, and_true] at h ⊢
  simp_all [cycle5, swap_apply_def]
  grind

omit [Fintype α] in
theorem two_pairs_comm_fixed {σ : Perm α} {a b c d e : α}
    (hp : TwoPairs σ a b c d) (hn : [a, b, c, d, e].Nodup) (he : σ e = e) :
    Path4 (comm σ (cycle3 a c e)) a b d e := by
  rcases hp with ⟨_, ha, hb, hc, hd⟩
  rw [comm_cycle3, ha, hc, he]
  simp only [Path4, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, not_or, and_true] at hn ⊢
  simp_all [cycle3, swap_apply_def]
  grind

omit [Fintype α] in
theorem two_pairs_comm_moved {σ : Perm α} {a b c d e : α}
    (hp : TwoPairs σ a b c d) (hn : [a, b, c, d, e].Nodup) (he : σ e ≠ e) :
    ThreeExtra (comm σ (cycle3 a c e)) b d (σ e) a e := by
  have hinj := σ.injective
  rcases hp with ⟨_, ha, hb, hc, hd⟩
  have hn' : [a, b, c, d, e, σ e].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, not_or, and_true] at hn ⊢
    grind
  rw [comm_cycle3, ha, hc]
  simp only [ThreeExtra, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, not_or, and_true] at hn' ⊢
  simp_all [cycle3, swap_apply_def]
  grind

theorem exists_fifth {a b c d : α} (h5 : 5 ≤ Nat.card α)
    (hn : [a, b, c, d].Nodup) : ∃ e, [a, b, c, d, e].Nodup := by
  have hcard : ({a, b, c, d} : Finset α).card < (Finset.univ : Finset α).card := by
    have h₁ := Finset.card_insert_le a ({b, c, d} : Finset α)
    have h₂ := Finset.card_insert_le b ({c, d} : Finset α)
    have h₃ := Finset.card_insert_le c ({d} : Finset α)
    simp only [Finset.card_singleton] at h₃
    simp only [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨e, _, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨e, ?_⟩
  simp_all [List.nodup_cons]
  grind

/-- A nonidentity normal subgroup contains a three-cycle once a four-point path is known. -/
theorem three_of_path4 {N : Subgroup (Perm α)} (hN : NormalInAlternating N)
    {σ : Perm α} (hσ : σ ∈ N) {a b c d : α} (h : Path4 σ a b c d) :
    ∃ τ ∈ N, τ.IsThreeCycle := by
  have habc : [a, b, c].Nodup := by grind [Path4, List.nodup_cons]
  have hadb : [a, d, b].Nodup := by grind [Path4, List.nodup_cons]
  exact ⟨cycle3 a d b, comm_path4 h ▸ comm_mem hN hσ (cycle3_even habc),
    cycle3_isThreeCycle hadb⟩

/-- The first commutator is a five-cycle, to which the four-point construction applies. -/
theorem three_of_three_extra {N : Subgroup (Perm α)} (hN : NormalInAlternating N)
    {σ : Perm α} (hσ : σ ∈ N) {a b c d e : α} (h : ThreeExtra σ a b c d e) :
    ∃ τ ∈ N, τ.IsThreeCycle := by
  have habd : [a, b, d].Nodup := by grind [ThreeExtra, List.nodup_cons]
  have hn : [a, d, c, e, b].Nodup := by grind [ThreeExtra, List.nodup_cons]
  have hm : cycle5 a d c e b ∈ N :=
    comm_three_extra h ▸ comm_mem hN hσ (cycle3_even habd)
  exact three_of_path4 hN hm (cycle5_path hn)

/-- A fifth point is fixed or belongs to a further orbit; both cases give a three-cycle. -/
theorem three_of_two_pairs {N : Subgroup (Perm α)} (h5 : 5 ≤ Nat.card α)
    (hN : NormalInAlternating N) {σ : Perm α} (hσ : σ ∈ N)
    {a b c d : α} (h : TwoPairs σ a b c d) : ∃ τ ∈ N, τ.IsThreeCycle := by
  obtain ⟨e, hn⟩ := exists_fifth h5 h.1
  have hace : [a, c, e].Nodup := by grind [List.nodup_cons]
  have hm := comm_mem hN hσ (cycle3_even hace)
  by_cases he : σ e = e
  · exact three_of_path4 hN hm (two_pairs_comm_fixed h hn he)
  · exact three_of_three_extra hN hm (two_pairs_comm_moved h hn he)

/-- Generation by three-cycles and their conjugacy inside the alternating group. -/
theorem eq_alternating_of_three {N : Subgroup (Perm α)} (h5 : 5 ≤ Nat.card α)
    (hle : N ≤ alternatingGroup α) (hN : NormalInAlternating N)
    (hthree : ∃ σ ∈ N, σ.IsThreeCycle) : N = alternatingGroup α := by
  apply le_antisymm hle
  rw [← closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro τ hτ
  obtain ⟨σ, hσ, hs⟩ := hthree
  have hconj := alternatingGroup.isThreeCycle_isConj h5
    (σ := ⟨σ, hs.mem_alternatingGroup⟩) (τ := ⟨τ, hτ.mem_alternatingGroup⟩) hs hτ
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have heq : (g : Perm α) * σ * (g : Perm α)⁻¹ = τ := congrArg Subtype.val hg
  exact heq ▸ hN g g.property σ hσ

/-- Convert the shared three-cycle argument to the standard statement of simplicity. -/
theorem simple_of_three_cycle_production (h5 : 5 ≤ Nat.card α)
    (produce : ∀ (N : Subgroup (Perm α)), N ≤ alternatingGroup α →
      NormalInAlternating N → ∀ σ ∈ N, σ ≠ 1 → ∃ τ ∈ N, τ.IsThreeCycle) :
    IsSimpleGroup (alternatingGroup α) := by
  have hnt : Nontrivial (alternatingGroup α) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := ?_ }
  intro K hK
  let N := K.map (alternatingGroup α).subtype
  have hle : N ≤ alternatingGroup α := by
    rintro σ ⟨x, _, rfl⟩
    exact x.property
  have hnormal : NormalInAlternating N := by
    rintro g hg x ⟨y, hy, rfl⟩
    exact ⟨(⟨g, hg⟩ : alternatingGroup α) * y * (⟨g, hg⟩ : alternatingGroup α)⁻¹,
      hK.conj_mem y hy ⟨g, hg⟩, rfl⟩
  rcases N.bot_or_exists_ne_one with hbot | ⟨σ, hσ, hne⟩
  · left
    apply bot_unique
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.val_injective
    have hm : (x : Perm α) ∈ N := ⟨x, hx, rfl⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.mp hm
  · right
    have heq := eq_alternating_of_three h5 hle hnormal (produce N hle hnormal σ hσ hne)
    apply top_unique
    intro x _
    have hm : (x : Perm α) ∈ N := by rw [heq]; exact x.property
    obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hm
    have hyx : y = x := Subtype.ext he
    exact hyx ▸ hy

end DesignExamples.Alternating
