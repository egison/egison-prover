import DesignExamples.Common

namespace DesignExamples.Involution

variable {A : Type*} [DecidableEq A]

def Conditions (S : Finset A) (σ : A → A) : Prop :=
  (∀ x ∈ S, σ x ∈ S) ∧ (∀ x ∈ S, σ (σ x) = x) ∧ (∀ x ∈ S, σ x ≠ x)

def remainder (S : Finset A) (σ : A → A) (x : A) : Finset A :=
  (S.erase x).erase (σ x)

theorem pair_evidence (S : Finset A) (σ : A → A) (x : A) (R : Multiset A)
    (heq : S.val = x ::ₘ σ x ::ₘ R) :
    x ∈ S ∧ σ x ∈ S ∧ σ x ≠ x ∧ R = (remainder S σ x).val := by
  have hx : x ∈ S := by change x ∈ S.val; simp [heq]
  have hy : σ x ∈ S := by change σ x ∈ S.val; simp [heq]
  have hne : σ x ≠ x := by
    have hn := S.nodup
    rw [heq, Multiset.nodup_cons] at hn
    exact fun h => hn.1 (by simp [h])
  refine ⟨hx, hy, hne, ?_⟩
  simp [remainder, Finset.erase_val, heq]

theorem pair_remainder (S : Finset A) (σ : A → A) (x : A)
    (hx : x ∈ S) (h : Conditions S σ) :
    remainder S σ x ⊂ S ∧ Conditions (remainder S σ x) σ ∧
      S.card = (remainder S σ x).card + 2 := by
  obtain ⟨hclosed, hinvol, hfixed⟩ := h
  have hy := hclosed x hx
  have hne := hfixed x hx
  have hsub : remainder S σ x ⊆ S :=
    fun z hz => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
  have hlt : remainder S σ x ⊂ S :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨x, hx, by simp [remainder]⟩
  have hc : ∀ z ∈ remainder S σ x, σ z ∈ remainder S σ x := by
    intro z hz
    have hzS := hsub hz
    have hzx := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzy := (Finset.mem_erase.mp hz).1
    have hσzx : σ z ≠ x := by
      intro he
      have : z = σ x := (hinvol z hzS).symm.trans (congrArg σ he)
      exact hzy this
    have hσzy : σ z ≠ σ x := by
      intro he
      have : z = x := (hinvol z hzS).symm.trans
        ((congrArg σ he).trans (hinvol x hx))
      exact hzx this
    exact Finset.mem_erase.mpr ⟨hσzy, Finset.mem_erase.mpr ⟨hσzx, hclosed z hzS⟩⟩
  have hn := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne, hy⟩)
  have hm := Finset.card_erase_add_one hx
  refine ⟨hlt, ⟨hc, fun z hz => hinvol z (hsub hz),
    fun z hz => hfixed z (hsub hz)⟩, ?_⟩
  dsimp [remainder]
  omega

theorem involution_card_even (S : Finset A) (σ : A → A) (h : Conditions S σ) :
    2 ∣ S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    obtain rfl | ⟨x, hx⟩ := S.eq_empty_or_nonempty
    · simp
    obtain ⟨hlt, hrest, hcard⟩ := pair_remainder S σ x hx h
    obtain ⟨k, hk⟩ := ih (remainder S σ x) hlt hrest
    exact ⟨k + 1, by omega⟩

theorem involution_sum_zero {B : Type*} [AddCommGroup B]
    (S : Finset A) (σ : A → A) (w : A → B)
    (h : Conditions S σ) (hw : ∀ x ∈ S, w (σ x) = -w x) :
    ∑ x ∈ S, w x = 0 := by
  induction S using Finset.strongInduction with
  | H S ih =>
    obtain rfl | ⟨x, hx⟩ := S.eq_empty_or_nonempty
    · simp
    obtain ⟨hlt, hrest, _⟩ := pair_remainder S σ x hx h
    have hi := ih (remainder S σ x) hlt hrest
      (fun z hz => hw z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)))
    have hy : σ x ∈ S.erase x := Finset.mem_erase.mpr ⟨h.2.2 x hx, h.1 x hx⟩
    rw [← Finset.add_sum_erase S w hx, ← Finset.add_sum_erase (S.erase x) w hy]
    change w x + (w (σ x) + ∑ z ∈ remainder S σ x, w z) = 0
    rw [hi, hw x hx]
    simp

def toggle (a : A) (U : Finset A) : Finset A :=
  if a ∈ U then U.erase a else insert a U

theorem toggle_conditions (S : Finset A) (a : A) (ha : a ∈ S) :
    Conditions S.powerset (toggle a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    rw [Finset.mem_powerset] at hU ⊢
    by_cases hm : a ∈ U
    · simpa [toggle, hm] using (Finset.erase_subset a U).trans hU
    · simpa [toggle, hm] using (Finset.insert_subset_iff.mpr ⟨ha, hU⟩)
  · intro U _
    by_cases hm : a ∈ U <;> simp [toggle, hm]
  · intro U _ he
    by_cases hm : a ∈ U
    · have hnot : a ∉ toggle a U := by simp [toggle, hm]
      exact hnot (he.symm ▸ hm)
    · have hyes : a ∈ toggle a U := by simp [toggle, hm]
      exact hm (he ▸ hyes)

theorem toggle_sign (a : A) (U : Finset A) :
    (-1 : Int) ^ (toggle a U).card = -((-1 : Int) ^ U.card) := by
  by_cases hm : a ∈ U
  · have hc := Finset.card_erase_add_one hm
    simp only [toggle, if_pos hm]
    conv_rhs => rw [← hc, pow_succ]
    ring
  · simp [toggle, hm, Finset.card_insert_of_notMem hm, pow_succ]

theorem alternating_powerset_sum (S : Finset A) (a : A) (ha : a ∈ S) :
    ∑ U ∈ S.powerset, (-1 : Int) ^ U.card = 0 :=
  involution_sum_zero S.powerset (toggle a) (fun U => (-1 : Int) ^ U.card)
    (toggle_conditions S a ha) (fun U _ => toggle_sign a U)

end DesignExamples.Involution
