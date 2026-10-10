import DesignExamples.ConfigurationRulesCommon

namespace DesignExamples.Ordinary.ConfigurationRules

variable {G : Type*} [Group G]

theorem cancel_all (w : List G) :
    ∀ pre g post, w = pre ++ g :: g⁻¹ :: post →
      (pre ++ post).prod = w.prod ∧ (pre ++ post).length + 2 = w.length := by
  intro pre g post hw
  subst w
  constructor
  · exact (DesignExamples.GroupWords.cancel_pair pre g post).symm
  · simp only [List.length_append, List.length_cons]
    omega

def cancelAt (w : List G)
    (cut : {c // DesignExamples.ConfigurationRules.InverseMatch w c}) :
    {r // DesignExamples.ConfigurationRules.CancelGood w r} :=
  DesignExamples.ConfigurationRules.applyCertified
    DesignExamples.ConfigurationRules.InverseMatch
    DesignExamples.ConfigurationRules.inverseResult
    DesignExamples.ConfigurationRules.CancelGood
    DesignExamples.ConfigurationRules.cancel_all_matches w cut

theorem all_equal_cuts_join {A : Type*} (w : List A) :
    ∀ p a s q b t, w = p ++ a :: a :: s → w = q ++ b :: b :: t →
      DesignExamples.AdjacentCancellation.Join (p ++ s) (q ++ t) := by
  intro p a s q b t hp hq
  exact DesignExamples.AdjacentCancellation.local_confluence
    ⟨p, a, s, hp, rfl⟩ ⟨q, b, t, hq, rfl⟩

section Tails
variable {V : Type*} [DecidableEq V] {D : DesignExamples.LGV.SimpleDigraph V}

theorem tail_swaps_all (hac : D.IsAcyclic)
    (p q : DesignExamples.LGV.SimpleDigraph.Path D) :
    ∀ preI v tailI preJ tailJ,
      p.vertices = preI ++ v :: tailI → q.vertices = preJ ++ v :: tailJ →
      ∃ pq : DesignExamples.LGV.SimpleDigraph.Path D × DesignExamples.LGV.SimpleDigraph.Path D,
        (pq.1.vertices, pq.2.vertices) = (preI ++ v :: tailJ, preJ ++ v :: tailI) ∧
        pq.1.start = p.start ∧ pq.1.finish = q.finish ∧
        pq.2.start = q.start ∧ pq.2.finish = p.finish := by
  intro preI v tailI preJ tailJ hI hJ
  let cut : {c // DesignExamples.ConfigurationRules.TailMatch (p.vertices, q.vertices) c} :=
    ⟨⟨preI, v, tailI, preJ, tailJ⟩, Prod.ext hI hJ⟩
  exact ⟨DesignExamples.ConfigurationRules.swapPathsAt p q cut,
    DesignExamples.ConfigurationRules.swapPathsAt_vertex_form hac p q cut,
    DesignExamples.ConfigurationRules.swapPathsAt_endpoints p q cut⟩
end Tails
end DesignExamples.Ordinary.ConfigurationRules
