import DesignExamples.ListCuts

namespace DesignExamples.TwoCancellations

open ListCuts

variable {G : Type*} [Group G]

def Good (w r : List G) : Prop := r.prod = w.prod ∧ r.length + 4 = w.length

def InversePair (c : Cut G) : Prop := c.second = c.first⁻¹

def GoodMany (n : Nat) (w r : List G) : Prop := r.prod = w.prod ∧ r.length + 2 * n = w.length

instance [DecidableEq G] : DecidablePred (InversePair (G := G)) :=
  fun c => inferInstanceAs (Decidable (c.second = c.first⁻¹))

def removeTwo (c₁ c₂ : Cut G) : List G := c₁.pre ++ (c₂.pre ++ c₂.post)

-- 二箇所の逆元対を消去する、両版で共通の数学的推論。
theorem two_cancel_identity (pre : List G) (g : G) (mid : List G)
    (k : G) (post : List G) :
    Good (pre ++ g :: g⁻¹ :: (mid ++ k :: k⁻¹ :: post)) (pre ++ (mid ++ post)) := by
  constructor
  · simp [List.prod_append]
  · simp only [List.length_append, List.length_cons]
    omega

-- 個々の分解の証拠を、一つのリストの等式へ組み合わせる。
theorem pair_sound {w : List G} (c₁ c₂ : Cut G)
    (h₁ : c₁.source = w ∧ InversePair c₁)
    (h₂ : c₂.source = c₁.post ∧ InversePair c₂) : Good w (removeTwo c₁ c₂) := by
  rcases c₁ with ⟨pre, g, gi, tail⟩
  rcases c₂ with ⟨mid, k, ki, post⟩
  simp only [Cut.source, InversePair] at h₁ h₂
  rcases h₁ with ⟨rfl, rfl⟩
  rcases h₂ with ⟨rfl, rfl⟩
  exact two_cancel_identity pre g mid k post

-- 後半についての証明を、前半と一組の逆元を持つ語へ戻す。
theorem extend_good {n : Nat} {w r : List G} (c : Cut G)
    (hc : c.source = w ∧ InversePair c) (hr : GoodMany n c.post r) :
    GoodMany (n + 1) w (c.pre ++ r) := by
  rcases c with ⟨pre, g, gi, post⟩
  simp only [Cut.source, InversePair] at hc
  rcases hc with ⟨rfl, rfl⟩
  rcases hr with ⟨hprod, hlen⟩
  change r.length + 2 * n = post.length at hlen
  constructor
  · simpa [List.prod_append] using congrArg (fun x => pre.prod * x) hprod
  · simp only [List.length_append, List.length_cons]
    omega

variable [DecidableEq G]

-- 左の位置、次に右の位置を昇順で選ぶ。第二の対は第一の対の後から選ぶ。
def plain (w : List G) : List (List G) :=
  ((cuts w).filter fun c => decide (InversePair c)).flatMap fun c₁ =>
    ((cuts c₁.post).filter fun c => decide (InversePair c)).map (removeTwo c₁)

def plainMany : Nat → List G → List (List G)
  | 0, w => [w]
  | n + 1, w =>
    ((cuts w).filter fun c => decide (InversePair c)).flatMap fun c =>
      (plainMany n c.post).map fun r => c.pre ++ r

theorem plainMany_two (w : List G) : plainMany 2 w = plain w := by
  simp only [plainMany, plain, List.map_cons, List.map_nil, List.map_flatMap]
  congr 1
  funext c
  change (List.flatMap (fun a => [removeTwo c a]) _) = _
  rw [← List.map_eq_flatMap]

theorem repeated_identity_example : plain ([1, 1, 1, 1, 1] : List G) = [[1], [1], [1]] := by
  simp [plain, cuts, starts, prepend, InversePair, removeTwo]

def Matches (w r : List G) : Prop :=
  ∃ pre g mid k post,
    w = pre ++ g :: g⁻¹ :: (mid ++ k :: k⁻¹ :: post) ∧ r = pre ++ (mid ++ post)

def MatchesMany : Nat → List G → List G → Prop
  | 0, w, r => r = w
  | n + 1, w, r =>
    ∃ pre g post s,
      w = pre ++ g :: g⁻¹ :: post ∧ MatchesMany n post s ∧ r = pre ++ s

theorem mem_plainMany_iff {n : Nat} {w r : List G} :
    r ∈ plainMany n w ↔ MatchesMany n w r := by
  induction n generalizing w r with
  | zero => simp [plainMany, MatchesMany]
  | succ n ih =>
    simp only [plainMany, MatchesMany, List.mem_flatMap, List.mem_map,
      List.mem_filter, decide_eq_true_eq, mem_cuts_iff, ih]
    constructor
    · rintro ⟨c, ⟨hc, hp⟩, s, hs, rfl⟩
      refine ⟨c.pre, c.first, c.post, s, ?_, hs, rfl⟩
      simpa only [Cut.source, show c.second = c.first⁻¹ from hp] using hc.symm
    · rintro ⟨pre, g, post, s, rfl, hs, rfl⟩
      exact ⟨⟨pre, g, g⁻¹, post⟩, ⟨rfl, rfl⟩, s, hs, rfl⟩

-- 成功する分解をすべて列挙することも、具体的な列挙について証明する。
theorem mem_plain_iff {w r : List G} : r ∈ plain w ↔ Matches w r := by
  constructor
  · intro hr
    obtain ⟨c₁, hc₁, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hr
    simp only [List.mem_filter, decide_eq_true_eq] at hc₁ hc₂
    refine ⟨c₁.pre, c₁.first, c₂.pre, c₂.first, c₂.post, ?_, rfl⟩
    rw [← cuts_sound hc₁.1]
    simp only [Cut.source]
    rw [hc₁.2, ← cuts_sound hc₂.1]
    simp only [Cut.source]
    rw [show c₂.second = c₂.first⁻¹ from hc₂.2]
  · rintro ⟨pre, g, mid, k, post, rfl, rfl⟩
    let c₁ : Cut G := ⟨pre, g, g⁻¹, mid ++ k :: k⁻¹ :: post⟩
    let c₂ : Cut G := ⟨mid, k, k⁻¹, post⟩
    apply List.mem_flatMap.mpr
    refine ⟨c₁, List.mem_filter.mpr ⟨mem_cuts_source c₁, ?_⟩, ?_⟩
    · exact decide_eq_true rfl
    · apply List.mem_map.mpr
      refine ⟨c₂, List.mem_filter.mpr ⟨mem_cuts_source c₂, ?_⟩, rfl⟩
      exact decide_eq_true rfl

end DesignExamples.TwoCancellations
