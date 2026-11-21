import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcHolo_det_differentiableAt {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype n] [DecidableEq n] (M : E → Matrix n n ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) x) :
    DifferentiableAt ℂ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ s : Finset n, DifferentiableAt ℂ (fun b => ∏ i ∈ s, M b (σ i) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).fun_mul ih
  exact key _

end GlobalTheory.CompanionTheory.Ar.Flat
