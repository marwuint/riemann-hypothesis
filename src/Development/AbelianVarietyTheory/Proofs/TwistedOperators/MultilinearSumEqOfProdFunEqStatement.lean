import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfProdFunEq

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq : ∀ {ι κ : Type} [Fintype ι] {X : ι → Type} (V : ∀ l, Submodule ℂ (X l → ℂ))
    (Φ : MultilinearMap ℂ (fun l => V l) ℂ) (a : κ →₀ ℂ) (f g : κ → ∀ l, V l),
    (∀ z : ∀ l, X l, (a.sum fun c b => b * ∏ l, (f c l : X l → ℂ) (z l)) = a.sum fun c b => b * ∏ l, (g c l : X l → ℂ) (z l)) →
    (a.sum fun c b => b * Φ (f c)) = a.sum fun c b => b * Φ (g c) := by
  exact @GlobalTheory.multilinear_sum_eq_of_prod_fun_eq
