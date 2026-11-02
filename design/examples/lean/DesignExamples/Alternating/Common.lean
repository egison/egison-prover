import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
Shared mathematics for a cycle-based proof of simplicity of the alternating group.
The simplicity theorem from `Alternating.Simple` is deliberately not imported.
Multiplication acts from right to left; `cycle3 a b c` sends a to b to c to a.
-/

namespace DesignExamples.Alternating

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

def cycle3 (a b c : α) : Perm α := swap a b * swap b c

def cycle5 (a b c d e : α) : Perm α :=
  swap a b * swap b c * swap c d * swap d e

def comm (σ τ : Perm α) : Perm α := σ * τ * σ⁻¹ * τ⁻¹

/-- A path of four distinct points in an orbit of a permutation. -/
def Path4 (σ : Perm α) (a b c d : α) : Prop :=
  [a, b, c, d].Nodup ∧ σ a = b ∧ σ b = c ∧ σ c = d

/-- A three-cycle together with a moved point outside that cycle. -/
def ThreeExtra (σ : Perm α) (a b c d e : α) : Prop :=
  [a, b, c, d, e].Nodup ∧ σ a = b ∧ σ b = c ∧ σ c = a ∧ σ d = e

/-- Two disjoint two-cycles; the permutation may move further points. -/
def TwoPairs (σ : Perm α) (a b c d : α) : Prop :=
  [a, b, c, d].Nodup ∧ σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c

/-- Conjugation by an even permutation preserves the subgroup. -/
def NormalInAlternating (N : Subgroup (Perm α)) : Prop :=
  ∀ g ∈ alternatingGroup α, ∀ x ∈ N, g * x * g⁻¹ ∈ N

theorem cycle3_isThreeCycle {a b c : α} (h : [a, b, c].Nodup) :
    (cycle3 a b c).IsThreeCycle := by
  have hab : a ≠ b := by grind [List.nodup_cons]
  have hac : a ≠ c := by grind [List.nodup_cons]
  have hbc : b ≠ c := by grind [List.nodup_cons]
  simpa only [cycle3, swap_comm b a] using
    isThreeCycle_swap_mul_swap_same hab.symm hbc hac

theorem cycle3_even {a b c : α} (h : [a, b, c].Nodup) :
    cycle3 a b c ∈ alternatingGroup α :=
  (cycle3_isThreeCycle h).mem_alternatingGroup

omit [Fintype α] in
theorem conjugate_cycle3 (σ : Perm α) (a b c : α) :
    σ * cycle3 a b c * σ⁻¹ = cycle3 (σ a) (σ b) (σ c) := by
  calc
    _ = (σ * swap a b * σ⁻¹) * (σ * swap b c * σ⁻¹) := by
      unfold cycle3
      group
    _ = _ := by rw [← swap_apply_apply, ← swap_apply_apply]; rfl

omit [Fintype α] in
theorem comm_cycle3 (σ : Perm α) (a b c : α) :
    comm σ (cycle3 a b c) = cycle3 (σ a) (σ b) (σ c) * (cycle3 a b c)⁻¹ := by
  rw [comm, conjugate_cycle3]

theorem comm_mem {N : Subgroup (Perm α)} (hN : NormalInAlternating N)
    {σ τ : Perm α} (hσ : σ ∈ N) (hτ : τ ∈ alternatingGroup α) :
    comm σ τ ∈ N := by
  have h := N.mul_mem hσ (hN τ hτ σ⁻¹ (N.inv_mem hσ))
  simpa [comm, mul_assoc] using h

omit [Fintype α] in
theorem comm_path4 {σ : Perm α} {a b c d : α} (h : Path4 σ a b c d) :
    comm σ (cycle3 a b c) = cycle3 a d b := by
  rcases h with ⟨hn, ha, hb, hc⟩
  rw [comm_cycle3, ha, hb, hc]
  simp only [List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hn
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hxc : x = c <;> by_cases hxd : x = d <;>
    simp_all [cycle3, Equiv.swap_apply_def] <;> grind

omit [Fintype α] in
theorem comm_three_extra {σ : Perm α} {a b c d e : α}
    (h : ThreeExtra σ a b c d e) :
    comm σ (cycle3 a b d) = cycle5 a d c e b := by
  rcases h with ⟨hn, ha, hb, hc, hd⟩
  rw [comm_cycle3, ha, hb, hd]
  simp only [List.nodup_cons, List.mem_cons, not_or,
    List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at hn
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hxc : x = c <;> by_cases hxd : x = d <;> by_cases hxe : x = e <;>
    simp_all [cycle3, cycle5, Equiv.swap_apply_def] <;> grind

end DesignExamples.Alternating
