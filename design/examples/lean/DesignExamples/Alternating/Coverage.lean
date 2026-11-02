import DesignExamples.Alternating.Common

/-! Exhaustive local orbit configurations, proved without a simplicity theorem. -/

namespace DesignExamples.Alternating

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- Following a moved point gives a two-cycle, a three-cycle, or four distinct points. -/
theorem orbit_at_cases (σ : Perm α) (a : α) (ha : σ a ≠ a) :
    (∃ b, [a, b].Nodup ∧ σ a = b ∧ σ b = a) ∨
    (∃ b c, [a, b, c].Nodup ∧ σ a = b ∧ σ b = c ∧ σ c = a) ∨
    (∃ b c d, Path4 σ a b c d) := by
  have hinj := σ.injective
  by_cases h2 : σ (σ a) = a
  · exact Or.inl ⟨σ a, by simp [Ne.symm ha], rfl, h2⟩
  by_cases h3 : σ (σ (σ a)) = a
  · refine Or.inr (Or.inl ⟨σ a, σ (σ a), ?_, rfl, rfl, h3⟩)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, not_or, and_true]
    grind
  · refine Or.inr (Or.inr ⟨σ a, σ (σ a), σ (σ (σ a)), ?_, rfl, rfl, rfl⟩)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, not_or, and_true]
    grind

/-- Ordinary disjunction used on both sides of the proof comparison. -/
def Cases (σ : Perm α) : Prop :=
  (∃ a b c, [a, b, c].Nodup ∧ σ = cycle3 a b c) ∨
  (∃ a b c d, Path4 σ a b c d) ∨
  (∃ a b c d e, ThreeExtra σ a b c d e) ∨
  (∃ a b c d, TwoPairs σ a b c d)

/-- Every nonidentity even permutation has one of the four local configurations. -/
theorem cases_exhaustive (σ : Perm α) (hσ : σ ∈ alternatingGroup α) (hne : σ ≠ 1) :
    Cases σ := by
  have hinj := σ.injective
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra! h
    exact hne (Equiv.ext h)
  rcases orbit_at_cases σ a ha with ⟨b, hab, hb, hba⟩ |
    ⟨b, c, habc, hb, hc, hca⟩ | ⟨b, c, d, h⟩
  · have hab' : a ≠ b := by simpa using hab
    have hswap : σ ≠ swap a b := by
      intro h
      have hs := hσ
      rw [h, mem_alternatingGroup, sign_swap hab'] at hs
      norm_num at hs
    obtain ⟨c, hc⟩ : ∃ c, σ c ≠ swap a b c := by
      by_contra! h
      exact hswap (Equiv.ext h)
    have hca : c ≠ a := by intro h; subst c; simp [hb] at hc
    have hcb : c ≠ b := by intro h; subst c; simp [hba] at hc
    have hc' : σ c ≠ c := by simpa [swap_apply_def, hca, hcb] using hc
    rcases orbit_at_cases σ c hc' with ⟨d, hcd, hd, hdc⟩ |
      ⟨d, e, hcde, hd, he, hec⟩ | ⟨d, e, f, h⟩
    · refine Or.inr (Or.inr (Or.inr ⟨a, b, c, d, ?_, hb, hba, hd, hdc⟩))
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, not_or, and_true] at hcd ⊢
      grind
    · refine Or.inr (Or.inr (Or.inl ⟨c, d, e, a, b, ?_, hd, he, hec, hb⟩))
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, not_or, and_true] at hcde ⊢
      grind
    · exact Or.inr (Or.inl ⟨c, d, e, f, h⟩)
  · by_cases heq : σ = cycle3 a b c
    · exact Or.inl ⟨a, b, c, habc, heq⟩
    obtain ⟨d, hd⟩ : ∃ d, σ d ≠ cycle3 a b c d := by
      by_contra! h
      exact heq (Equiv.ext h)
    have hda : d ≠ a := by
      intro h; subst d
      simp_all [cycle3, swap_apply_def, List.nodup_cons]
    have hdb : d ≠ b := by
      intro h; subst d
      simp_all [cycle3, swap_apply_def, List.nodup_cons]
      grind
    have hdc : d ≠ c := by
      intro h; subst d
      simp_all [cycle3, List.nodup_cons]
    have hd' : σ d ≠ d := by
      simpa [cycle3, swap_apply_def, hda, hdb, hdc] using hd
    refine Or.inr (Or.inr (Or.inl ⟨a, b, c, d, σ d, ?_, hb, hc, hca, rfl⟩))
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, not_or, and_true] at habc ⊢
    grind
  · exact Or.inr (Or.inl ⟨a, b, c, d, h⟩)

end DesignExamples.Alternating
