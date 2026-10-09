import DesignExamples.Common

namespace DesignExamples.WalkPaths

variable {A : Type*}

def Walk (E : A → A → Prop) (s t : A) (w : List A) : Prop :=
  w.head? = some s ∧ w.getLast? = some t ∧ w.IsChain E

def Path (E : A → A → Prop) (s t : A) (w : List A) : Prop :=
  Walk E s t w ∧ w.Nodup

theorem splice_chain (E : A → A → Prop) (pre : List A) (v : A) (mid post : List A)
    (h : (pre ++ v :: (mid ++ v :: post)).IsChain E) :
    (pre ++ v :: post).IsChain E := by
  have hp := (List.isChain_split.mp h).1
  have hs := ((List.isChain_split.mp h).2.tail).right_of_append
  exact List.isChain_split.mpr ⟨hp, hs⟩

theorem splice_walk (E : A → A → Prop) (s t : A)
    (pre : List A) (v : A) (mid post : List A)
    (h : Walk E s t (pre ++ v :: (mid ++ v :: post))) :
    Walk E s t (pre ++ v :: post) := by
  refine ⟨?_, ?_, splice_chain E pre v mid post h.2.2⟩
  · cases pre <;> simpa using h.1
  · cases post with
    | nil => simpa [List.getLast?_cons, List.getLast?_append] using h.2.1
    | cons a l => simpa [List.getLast?_cons, List.getLast?_append] using h.2.1

theorem walk_to_path (E : A → A → Prop) (s t : A) (w : List A)
    (h : Walk E s t w) : ∃ p, Path E s t p ∧ p.length ≤ w.length := by
  classical
  suffices aux : ∀ n, ∀ w : List A, w.length = n → Walk E s t w →
      ∃ p, Path E s t p ∧ p.length ≤ w.length from aux w.length w rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hw
    by_cases hnd : w.Nodup
    · exact ⟨w, ⟨hw, hnd⟩, le_rfl⟩
    obtain ⟨pre, v, mid, post, rfl⟩ := repeated_split w hnd
    have hw' := splice_walk E s t pre v mid post hw
    have hlt : (pre ++ v :: post).length < n := by simp_all; omega
    obtain ⟨p, hp, hlen⟩ := ih _ hlt (pre ++ v :: post) rfl hw'
    refine ⟨p, hp, ?_⟩
    simp only [List.length_append, List.length_cons] at *
    omega

theorem singleton_path (E : A → A → Prop) (s : A) : Path E s s [s] := by
  simp [Path, Walk]

end DesignExamples.WalkPaths
