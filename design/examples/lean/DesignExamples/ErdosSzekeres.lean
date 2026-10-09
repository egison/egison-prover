import DesignExamples.Common

namespace DesignExamples.ErdosSzekeres

def Triple {A : Type*} [LT A] (f : Fin 5 → A) (i j k : Fin 5) : Prop :=
  i < j ∧ j < k ∧
    ((f i < f j ∧ f j < f k) ∨ (f k < f j ∧ f j < f i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_case : ∀ f : Fin 5 → Fin 5, Function.Injective f →
    ∃ i j k, Triple f i j k := by
  unfold Triple Function.Injective
  decide

theorem erdos_szekeres_five {A : Type*} [LinearOrder A]
    (f : Fin 5 → A) (hf : Function.Injective f) : ∃ i j k, Triple f i j k := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = 5 := by simp [S, Finset.card_image_of_injective _ hf]
  let e : Fin 5 ≃o S := S.orderIsoOfFin hcard
  let g : Fin 5 → Fin 5 := fun i => e.symm ⟨f i, Finset.mem_image.mpr ⟨i, by simp, rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j he
    have hv := congrArg (fun k => (e k : A)) he
    exact hf (by simpa [g] using hv)
  have hlt : ∀ i j, g i < g j ↔ f i < f j := by
    intro i j
    exact e.symm.lt_iff_lt
  obtain ⟨i, j, k, hij, hjk, hmono⟩ := finite_case g hg
  refine ⟨i, j, k, hij, hjk, ?_⟩
  rcases hmono with hinc | hdec
  · exact Or.inl ⟨(hlt i j).mp hinc.1, (hlt j k).mp hinc.2⟩
  · exact Or.inr ⟨(hlt k j).mp hdec.1, (hlt j i).mp hdec.2⟩

-- Any longer sequence inherits the result by using its first five positions.
theorem erdos_szekeres_prefix {A : Type*} [LinearOrder A] {n : Nat} (hn : 5 ≤ n)
    (f : Fin n → A) (hf : Function.Injective f) :
    ∃ i j k : Fin n, i < j ∧ j < k ∧
      ((f i < f j ∧ f j < f k) ∨ (f k < f j ∧ f j < f i)) := by
  let emb := Fin.castLEEmb hn
  obtain ⟨i, j, k, hij, hjk, hmono⟩ :=
    erdos_szekeres_five (f ∘ emb) (hf.comp emb.injective)
  exact ⟨emb i, emb j, emb k, hij, hjk, hmono⟩

def fourCounterexample : Fin 4 → Nat := ![2, 4, 1, 3]

theorem four_counterexample : Function.Injective fourCounterexample ∧
    ¬∃ i j k : Fin 4, i < j ∧ j < k ∧
      ((fourCounterexample i < fourCounterexample j ∧ fourCounterexample j < fourCounterexample k) ∨
        (fourCounterexample k < fourCounterexample j ∧ fourCounterexample j < fourCounterexample i)) := by
  unfold Function.Injective
  decide

theorem es_two {A : Type*} [LinearOrder A] (f : Fin 2 → A) (hf : Function.Injective f) :
    f 0 < f 1 ∨ f 1 < f 0 :=
  lt_or_gt_of_ne (hf.ne (by decide : (0 : Fin 2) ≠ 1))

end DesignExamples.ErdosSzekeres
