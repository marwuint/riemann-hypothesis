import Mathlib

private theorem UpperTheory.Reformulated.B.CoproductAdjoin.reindex {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ))
    (p : G → ℂ) {ι : Type} [Fintype ι] (a b : ι → G → ℂ) (h : ∀ i, a i ∈ A ∧ b i ∈ A)
    (hp : ∀ x k : G, p (x * k) = ∑ i, a i x * b i k) :
    ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
      (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k := by
  refine ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j),
    fun j => b ((Fintype.equivFin ι).symm j), fun j => h _, fun x k => ?_⟩
  rw [hp]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => a i x * b i k)).symm
