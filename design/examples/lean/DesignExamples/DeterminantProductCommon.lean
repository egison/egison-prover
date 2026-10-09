import DesignExamples.Common

namespace DesignExamples.DeterminantProduct

/-- Two distinct inputs with the same output. The order of witnesses follows the pattern. -/
def SharedImage {I J : Type*} (p : I → J) : Prop :=
  ∃ i k j, i ≠ j ∧ p i = k ∧ p j = k

theorem shared_image_of_not_injective {I J : Type*} (p : I → J)
    (hp : ¬Function.Injective p) : SharedImage p := by
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hp
  exact ⟨i, p i, j, hne, rfl, heq.symm⟩

end DesignExamples.DeterminantProduct
