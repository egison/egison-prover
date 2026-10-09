import DesignExamples.CauchyBinetCommon
import DesignExamples.DeterminantProduct

namespace DesignExamples.CauchyBinet

open Equiv Equiv.Perm Finset Function Matrix

/-- Cauchy–Binet, including empty matrices and the case of fewer columns than rows. -/
theorem cauchy_binet {m n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    det (A * B) = ∑ S ∈ (univ : Finset (Fin n)).powersetCard m, minorProduct A B S := by
  classical
  calc
    det (A * B) = ∑ p : Fin m → Fin n, ∑ σ : Perm (Fin m),
        ((sign σ : ℤ) : R) * ∏ i, A (σ i) (p i) * B (p i) i := by
      simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p : Fin m → Fin n with Injective p, ∑ σ : Perm (Fin m),
        ((sign σ : ℤ) : R) * ∏ i, A (σ i) (p i) * B (p i) i := by
      refine (sum_subset (filter_subset _ _) fun p _ hp =>
        DesignExamples.DeterminantProduct.noninjective_cancel ?_).symm
      simpa only [mem_filter_univ] using hp
    _ = _ := by
      rw [sum_injections_by_image]
      apply sum_congr rfl
      intro S hS
      have h : S.card = m := (mem_powersetCard.mp hS).2
      rw [minorProduct, dif_pos h, dif_pos h]
      exact sum_permutations (A.submatrix id (S.orderEmbOfFin h))
        (B.submatrix (S.orderEmbOfFin h) id)

end DesignExamples.CauchyBinet
