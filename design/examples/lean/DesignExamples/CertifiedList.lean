import Mathlib

namespace DesignExamples.CertifiedList

-- 各列挙結果に、その結果についての命題の証明を添える。
abbrev Certified {A : Type*} (P : A → Prop) := List {x : A // P x}

variable {A B : Type*} {P : A → Prop} {Q : B → Prop}

def values (xs : Certified P) : List A := xs.map Subtype.val

def keep (xs : Certified P) (test : A → Prop) [DecidablePred test] :
    Certified (fun x => P x ∧ test x) :=
  match xs with
  | [] => []
  | ⟨x, hx⟩ :: rest =>
    if ht : test x then ⟨x, hx, ht⟩ :: keep rest test else keep rest test

def mapWithProof (xs : Certified P) (f : A → B)
    (hf : ∀ x, P x → Q (f x)) : Certified Q :=
  xs.map fun x => ⟨f x.val, hf x.val x.property⟩

def bind (xs : Certified P) (f : ∀ x, P x → Certified Q) : Certified Q :=
  xs.flatMap fun x => f x.val x.property

theorem sound (xs : Certified P) {x : A} (hx : x ∈ values xs) : P x := by
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact y.property

theorem values_keep (xs : Certified P) (test : A → Prop) [DecidablePred test] :
    values (keep xs test) = (values xs).filter (fun x => decide (test x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨x, hx⟩
    simp [values] at ih
    by_cases ht : test x <;> simp [keep, values, ht, ih]

theorem values_map (xs : Certified P) (f : A → B)
    (hf : ∀ x, P x → Q (f x)) :
    values (mapWithProof xs f hf) = (values xs).map f := by
  simp [values, mapWithProof, List.map_map]

theorem values_bind (xs : Certified P) (f : ∀ x, P x → Certified Q)
    (g : A → List B) (hf : ∀ x hx, values (f x hx) = g x) :
    values (bind xs f) = (values xs).flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [values, bind] at ih
    simp [values] at hf
    simp [bind, values, List.map_append, hf, ih]

end DesignExamples.CertifiedList
