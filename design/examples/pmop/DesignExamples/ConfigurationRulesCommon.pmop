import DesignExamples.GroupWords
import DesignExamples.LocalConfluence
import DesignExamples.LGVCommon

/-! Logical quantification over configurations and transformations of supplied
configuration certificates. These definitions specify the proposed notation;
they do not implement a parser or an enumeration procedure. -/
namespace DesignExamples.ConfigurationRules

universe u v z

/-- Every binding satisfying the relation has the required property. -/
def AllMatches {T : Type u} {B : Type v}
    (rel : T → B → Prop) (target : T) (claim : B → Prop) : Prop :=
  ∀ binding, rel target binding → claim binding

/-- Universal quantification is equivalent to a claim about every certificate. -/
theorem allMatches_iff_certificates {T : Type u} {B : Type v}
    (rel : T → B → Prop) (target : T) (claim : B → Prop) :
    AllMatches rel target claim ↔ ∀ c : {b // rel target b}, claim c.val := by
  constructor
  · intro h c
    exact h c.val c.property
  · intro h b hb
    exact h ⟨b, hb⟩

theorem noMatch_iff_all_false {T : Type u} {B : Type v}
    (rel : T → B → Prop) (target : T) :
    (¬∃ b, rel target b) ↔ AllMatches rel target (fun _ => False) := by
  constructor
  · intro h b hb
    exact h ⟨b, hb⟩
  · rintro h ⟨b, hb⟩
    exact h b hb

/-- A universally correct rule can act on a supplied data certificate. -/
def applyCertified {T : Type u} {B : Type v} {U : Type z}
    (rel : T → B → Prop) (build : B → U) (post : T → U → Prop)
    (sound : ∀ t, AllMatches rel t (fun b => post t (build b)))
    (target : T) (cut : {b // rel target b}) : {result // post target result} :=
  ⟨build cut.val, sound target cut.val cut.property⟩

/-- The relation between the input and every permitted output of a rule. -/
def RuleRelation {T : Type u} {B : Type v} {U : Type z}
    (rel : T → B → Prop) (build : B → U) (target : T) (result : U) : Prop :=
  ∃ binding, rel target binding ∧ result = build binding

theorem all_rule_outputs {T : Type u} {B : Type v} {U : Type z}
    (rel : T → B → Prop) (build : B → U) (post : T → U → Prop)
    (sound : ∀ t, AllMatches rel t (fun b => post t (build b)))
    {target : T} {result : U} (h : RuleRelation rel build target result) :
    post target result := by
  obtain ⟨binding, hb, rfl⟩ := h
  exact sound target binding hb

section GroupWords
variable {G : Type*} [Group G]

structure InverseCut (G : Type*) where
  pre : List G
  g : G
  post : List G

def inverseSource (c : InverseCut G) : List G := c.pre ++ c.g :: c.g⁻¹ :: c.post
def inverseResult (c : InverseCut G) : List G := c.pre ++ c.post
def InverseMatch (w : List G) (c : InverseCut G) : Prop := w = inverseSource c
def CancelGood (w r : List G) : Prop := r.prod = w.prod ∧ r.length + 2 = w.length

/-- A compact ordinary Lean baseline, with all positions universally quantified. -/
theorem cancel_all_explicit (w : List G) :
    ∀ pre g post, w = pre ++ g :: g⁻¹ :: post →
      (pre ++ post).prod = w.prod ∧ (pre ++ post).length + 2 = w.length := by
  intro pre g post hw
  subst w
  constructor
  · exact (DesignExamples.GroupWords.cancel_pair pre g post).symm
  · simp only [List.length_append, List.length_cons]
    omega

/-- Exact relational meaning of the forallMatch example. -/
theorem cancel_all_matches (w : List G) :
    AllMatches InverseMatch w (fun c => CancelGood w (inverseResult c)) := by
  intro c hc
  exact cancel_all_explicit w c.pre c.g c.post hc

theorem cancel_all_iff_explicit (w : List G) :
    AllMatches InverseMatch w (fun c => CancelGood w (inverseResult c)) ↔
      ∀ pre g post, w = pre ++ g :: g⁻¹ :: post →
        (pre ++ post).prod = w.prod ∧ (pre ++ post).length + 2 = w.length := by
  constructor
  · intro h pre g post hw
    exact h ⟨pre, g, post⟩ hw
  · intro h c hc
    exact h c.pre c.g c.post hc

/-- An empty word admits no inverse-pair certificate, even though the universal law holds. -/
theorem no_inverse_cut_nil : ¬∃ c : InverseCut G, InverseMatch [] c := by
  rintro ⟨c, hc⟩
  have hlen := congrArg List.length hc
  simp [inverseSource] at hlen

def cancelAt (w : List G) (cut : {c // InverseMatch w c}) : {r // CancelGood w r} :=
  applyCertified InverseMatch inverseResult CancelGood cancel_all_matches w cut

def CancelsTo (w r : List G) : Prop := RuleRelation InverseMatch inverseResult w r

theorem cancelAt_relation (w : List G) (cut : {c // InverseMatch w c}) :
    CancelsTo w (cancelAt w cut).val := ⟨cut.val, cut.property, rfl⟩

theorem cancelsTo_good {w r : List G} (h : CancelsTo w r) : CancelGood w r :=
  all_rule_outputs InverseMatch inverseResult CancelGood cancel_all_matches h

theorem cancelsTo_iff_explicit (w r : List G) :
    CancelsTo w r ↔ ∃ pre g post,
      w = pre ++ g :: g⁻¹ :: post ∧ r = pre ++ post := by
  constructor
  · rintro ⟨c, hc, hr⟩
    exact ⟨c.pre, c.g, c.post, hc, hr⟩
  · rintro ⟨pre, g, post, hw, hr⟩
    exact ⟨⟨pre, g, post⟩, hw, hr⟩

/-- The same source admits two supplied cuts and possibly different output words. -/
theorem two_cuts (g k : G) :
    ∃ c₁ c₂ : {c // InverseMatch [g, g⁻¹, k, k⁻¹] c},
      (cancelAt _ c₁).val = [k, k⁻¹] ∧ (cancelAt _ c₂).val = [g, g⁻¹] := by
  refine ⟨⟨⟨[], g, [k, k⁻¹]⟩, rfl⟩, ⟨⟨[g, g⁻¹], k, []⟩, rfl⟩, rfl, rfl⟩
end GroupWords

section Joining
variable {A : Type*}

structure EqualCuts (A : Type*) where
  pre₁ : List A
  a : A
  post₁ : List A
  pre₂ : List A
  b : A
  post₂ : List A

def EqualCutsMatch (w : List A) (c : EqualCuts A) : Prop :=
  w = c.pre₁ ++ c.a :: c.a :: c.post₁ ∧ w = c.pre₂ ++ c.b :: c.b :: c.post₂

/-- Quantify over two independent selections in the same source. -/
theorem equal_cuts_all_join (w : List A) :
    AllMatches EqualCutsMatch w (fun c =>
      AdjacentCancellation.Join (c.pre₁ ++ c.post₁) (c.pre₂ ++ c.post₂)) := by
  intro c hc
  exact AdjacentCancellation.local_confluence
    ⟨c.pre₁, c.a, c.post₁, hc.1, rfl⟩ ⟨c.pre₂, c.b, c.post₂, hc.2, rfl⟩

theorem equal_cuts_iff_local (w : List A) :
    AllMatches EqualCutsMatch w (fun c =>
      AdjacentCancellation.Join (c.pre₁ ++ c.post₁) (c.pre₂ ++ c.post₂)) ↔
      ∀ u v, AdjacentCancellation.Step w u → AdjacentCancellation.Step w v →
        AdjacentCancellation.Join u v := by
  constructor
  · intro h u v hu hv
    obtain ⟨p, a, s, hp, rfl⟩ := hu
    obtain ⟨q, b, t, hq, rfl⟩ := hv
    exact h ⟨p, a, s, q, b, t⟩ ⟨hp, hq⟩
  · intro h c hc
    exact h _ _ ⟨c.pre₁, c.a, c.post₁, hc.1, rfl⟩
      ⟨c.pre₂, c.b, c.post₂, hc.2, rfl⟩
end Joining

section Tails
variable {V : Type*}

/-- A binding of both cuts; the source is reconstructed from these fields. -/
structure TailCut (V : Type*) where
  preI : List V
  v : V
  tailI : List V
  preJ : List V
  tailJ : List V
  deriving DecidableEq

def tailSource (c : TailCut V) : List V × List V :=
  (c.preI ++ c.v :: c.tailI, c.preJ ++ c.v :: c.tailJ)

def swapCut (c : TailCut V) : TailCut V :=
  {c with tailI := c.tailJ, tailJ := c.tailI}

theorem swapCut_involutive : Function.Involutive (swapCut (V := V)) := by
  intro c
  cases c
  rfl

def TailMatch (target : List V × List V) (c : TailCut V) : Prop := target = tailSource c
def ExchangesTo (target result : List V × List V) : Prop :=
  RuleRelation TailMatch (fun c => tailSource (swapCut c)) target result

theorem exchangesTo_iff_explicit (target result : List V × List V) :
    ExchangesTo target result ↔ ∃ preI v tailI preJ tailJ,
      target = (preI ++ v :: tailI, preJ ++ v :: tailJ) ∧
      result = (preI ++ v :: tailJ, preJ ++ v :: tailI) := by
  constructor
  · rintro ⟨c, hc, hr⟩
    exact ⟨c.preI, c.v, c.tailI, c.preJ, c.tailJ, hc, hr⟩
  · rintro ⟨preI, v, tailI, preJ, tailJ, ht, hr⟩
    exact ⟨⟨preI, v, tailI, preJ, tailJ⟩, ht, hr⟩

variable [DecidableEq V] {D : LGV.SimpleDigraph V}

/-- Reconstruct actual paths, including edge and endpoint evidence. -/
noncomputable def swapPathsAt (p q : LGV.SimpleDigraph.Path D)
    (cut : {c // TailMatch (p.vertices, q.vertices) c}) :
    LGV.SimpleDigraph.Path D × LGV.SimpleDigraph.Path D :=
  LGV.exchangeTailsOfCuts p q cut.val.v cut.val.preI cut.val.tailI
    cut.val.preJ cut.val.tailJ (congrArg Prod.fst cut.property) (congrArg Prod.snd cut.property)

theorem swapPathsAt_vertex_form (hac : D.IsAcyclic) (p q : LGV.SimpleDigraph.Path D)
    (cut : {c // TailMatch (p.vertices, q.vertices) c}) :
    ((swapPathsAt p q cut).1.vertices, (swapPathsAt p q cut).2.vertices) =
      tailSource (swapCut cut.val) := by
  have hI : p.vertices = cut.val.preI ++ cut.val.v :: cut.val.tailI :=
    congrArg Prod.fst cut.property
  have hJ : q.vertices = cut.val.preJ ++ cut.val.v :: cut.val.tailJ :=
    congrArg Prod.snd cut.property
  have h := LGV.exchangeTails_vertex_form hac p q cut.val.v cut.val.preI cut.val.tailI
    cut.val.preJ cut.val.tailJ hI hJ (by simp [hI]) (by simp [hJ])
  exact Prod.ext h.1 h.2

theorem swapPathsAt_endpoints (p q : LGV.SimpleDigraph.Path D)
    (cut : {c // TailMatch (p.vertices, q.vertices) c}) :
    (swapPathsAt p q cut).1.start = p.start ∧
    (swapPathsAt p q cut).1.finish = q.finish ∧
    (swapPathsAt p q cut).2.start = q.start ∧
    (swapPathsAt p q cut).2.finish = p.finish := by
  unfold swapPathsAt LGV.exchangeTailsOfCuts
  exact ⟨LGV.exchangeTails_fst_start _ _ _ _ _, LGV.exchangeTails_fst_finish _ _ _ _ _,
    LGV.exchangeTails_snd_start _ _ _ _ _, LGV.exchangeTails_snd_finish _ _ _ _ _⟩

theorem swapPathsAt_weight {K : Type*} [CommRing K] (wt : LGV.ArcWeight D K)
    (p q : LGV.SimpleDigraph.Path D)
    (cut : {c // TailMatch (p.vertices, q.vertices) c}) :
    LGV.pathWeight wt p * LGV.pathWeight wt q =
      LGV.pathWeight wt (swapPathsAt p q cut).1 * LGV.pathWeight wt (swapPathsAt p q cut).2 := by
  unfold swapPathsAt LGV.exchangeTailsOfCuts
  exact LGV.exchangeTails_weight _ _ _ _ _ _

/-- The vertex-pair rule applies to every cut, not just the canonical LGV choice. -/
theorem tail_swaps_all (hac : D.IsAcyclic) (p q : LGV.SimpleDigraph.Path D) :
    AllMatches TailMatch (p.vertices, q.vertices) (fun c =>
      ∃ pq : LGV.SimpleDigraph.Path D × LGV.SimpleDigraph.Path D,
        (pq.1.vertices, pq.2.vertices) = tailSource (swapCut c) ∧
        pq.1.start = p.start ∧ pq.1.finish = q.finish ∧
        pq.2.start = q.start ∧ pq.2.finish = p.finish) := by
  intro c hc
  exact ⟨swapPathsAt p q ⟨c, hc⟩, swapPathsAt_vertex_form hac p q ⟨c, hc⟩,
    swapPathsAt_endpoints p q ⟨c, hc⟩⟩
end Tails

/-- A reversible transformation of certificates induces an involution on sources
when selection agrees with the transformed certificate. C may itself be a
dependent pair packaging the source, bindings, and relation evidence. -/
theorem selected_involutive {X : Type u} {C : Type v}
    (source : C → X) (exchange : C → C) (select : X → C)
    (source_select : ∀ x, source (select x) = x)
    (exchange_twice : Function.Involutive exchange)
    (stable : ∀ x, select (source (exchange (select x))) = exchange (select x)) :
    Function.Involutive (fun x => source (exchange (select x))) := by
  intro x
  calc
    source (exchange (select (source (exchange (select x))))) =
        source (exchange (exchange (select x))) :=
      congrArg (fun c => source (exchange c)) (stable x)
    _ = source (select x) := congrArg source (exchange_twice (select x))
    _ = x := source_select x

namespace Counterexample
inductive Vertex | a | c | v | x | y | w | b | d deriving DecidableEq
open Vertex

def atV : TailCut Vertex := ⟨[a], v, [x, w, b], [c], [y, w, d]⟩
def laterAtW : TailCut Vertex := ⟨[a, v, y], w, [d], [c, v, x], [b]⟩

/-- Both stages choose a genuinely shared vertex of the current two paths. -/
theorem second_cut_valid : tailSource laterAtW = tailSource (swapCut atV) := rfl

/-- The second, different cut does not undo the first swap. -/
theorem different_cut_does_not_restore :
    tailSource (swapCut laterAtW) ≠ tailSource atV := by decide

/-- An acyclic graph realizes the counterexample with actual simple paths. -/
def edge (s t : Vertex) : Prop :=
  (s, t) ∈ [(a, v), (c, v), (v, x), (v, y), (x, w), (y, w), (w, b), (w, d)]

def rank : Vertex → Nat
  | a | c => 0
  | v => 1
  | x | y => 2
  | w => 3
  | b | d => 4

theorem edge_rank (s t : Vertex) (h : edge s t) : rank s < rank t := by
  cases s <;> cases t <;> simp_all [edge, rank]

theorem counterexample_paths :
    List.IsChain edge (tailSource atV).1 ∧ List.IsChain edge (tailSource atV).2 ∧
    List.IsChain edge (tailSource (swapCut atV)).1 ∧
    List.IsChain edge (tailSource (swapCut atV)).2 ∧
    List.IsChain edge (tailSource (swapCut laterAtW)).1 ∧
    List.IsChain edge (tailSource (swapCut laterAtW)).2 := by
  simp [tailSource, atV, laterAtW, swapCut, edge, List.isChain_cons_cons]

theorem counterexample_no_repeated_vertices :
    (tailSource atV).1.Nodup ∧ (tailSource atV).2.Nodup ∧
    (tailSource (swapCut atV)).1.Nodup ∧ (tailSource (swapCut atV)).2.Nodup ∧
    (tailSource (swapCut laterAtW)).1.Nodup ∧ (tailSource (swapCut laterAtW)).2.Nodup := by
  decide

end Counterexample
end DesignExamples.ConfigurationRules
