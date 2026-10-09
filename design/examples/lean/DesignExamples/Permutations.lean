import DesignExamples.Common

namespace DesignExamples.Permutations

variable {A : Type*} [DecidableEq A]

def Supported (S : Finset A) (π : Equiv.Perm A) : Prop :=
  ∀ x, x ∉ S → π x = x

def graph (S : Finset A) (π : Equiv.Perm A) : Multiset (A × A) :=
  S.val.map (fun x => (x, π x))

theorem graph_cases (S : Finset A) (π : Equiv.Perm A) (a : A)
    (ha : a ∈ S) (h : Supported S π) :
    (∃ R, π a = a ∧ graph S π = (a, a) ::ₘ R) ∨
    (∃ b c R, b ≠ a ∧ c ≠ a ∧ c ∈ S ∧ π a = b ∧ π c = a ∧
      graph S π = (a, b) ::ₘ (c, a) ::ₘ R) := by
  by_cases hfixed : π a = a
  · exact Or.inl ⟨graph (S.erase a) π, hfixed,
      by simp only [graph]; rw [take_one S a ha]; simp [hfixed]⟩
  let c := π.symm a
  have hpc : π c = a := π.apply_symm_apply a
  have hca : c ≠ a := by intro he; exact hfixed (he ▸ hpc)
  have hc : c ∈ S := by
    by_contra hn
    exact hca ((h c hn).symm.trans hpc)
  refine Or.inr ⟨π a, c, graph ((S.erase a).erase c) π,
    hfixed, hca, hc, rfl, hpc, ?_⟩
  simp only [graph]
  rw [take_two S a c ha hc hca]
  simp [hpc]

theorem factor_of_support (S : Finset A) (π : Equiv.Perm A) (h : Supported S π) :
    ∃ factors : List (Equiv.Perm A),
      factors.prod = π ∧ ∀ τ ∈ factors, Equiv.Perm.IsSwap τ := by
  induction S using Finset.strongInduction generalizing π with
  | H S ih =>
    obtain rfl | ⟨a, ha⟩ := S.eq_empty_or_nonempty
    · refine ⟨[], ?_, by simp⟩
      simpa using (Equiv.ext (fun x => (h x (by simp)).symm) : (1 : Equiv.Perm A) = π)
    by_cases hfixed : π a = a
    · apply ih (S.erase a) (Finset.erase_ssubset ha) π
      intro x hx
      by_cases he : x = a
      · simpa [he] using hfixed
      · exact h x (by simpa [he] using hx)
    let c := π.symm a
    have hpc : π c = a := π.apply_symm_apply a
    have hca : c ≠ a := by intro he; exact hfixed (he ▸ hpc)
    have hc : c ∈ S := by
      by_contra hn
      have he : c = a := (h c hn).symm.trans hpc
      exact hca he
    let π' := π * Equiv.swap a c
    have hsmall : Supported (S.erase a) π' := by
      intro x hx
      by_cases he : x = a
      · subst x
        simpa [π', Equiv.Perm.mul_apply] using hpc
      · have hxS : x ∉ S := by simpa [he] using hx
        have hxc : x ≠ c := by intro hec; exact hxS (hec ▸ hc)
        simpa [π', Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne he hxc] using h x hxS
    obtain ⟨factors, hprod, hswaps⟩ :=
      ih (S.erase a) (Finset.erase_ssubset ha) π' hsmall
    refine ⟨factors ++ [Equiv.swap a c], ?_, ?_⟩
    · simp [List.prod_append, hprod, π', mul_assoc]
    · intro τ hτ
      rcases List.mem_append.mp hτ with hτ | hτ
      · exact hswaps τ hτ
      · have he : τ = Equiv.swap a c := by simpa using hτ
        subst τ
        exact Equiv.Perm.swap_isSwap_iff.mpr hca.symm

theorem finite_permutation_factors [Fintype A] (π : Equiv.Perm A) :
    ∃ factors : List (Equiv.Perm A),
      factors.prod = π ∧ ∀ τ ∈ factors, Equiv.Perm.IsSwap τ :=
  factor_of_support Finset.univ π (fun x hx => False.elim (hx (Finset.mem_univ x)))

end DesignExamples.Permutations
