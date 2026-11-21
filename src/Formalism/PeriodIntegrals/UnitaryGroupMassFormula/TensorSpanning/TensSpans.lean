import Mathlib
import Formalism.PeriodIntegrals.KerTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorSpanning.MatHHOne

noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.KerTens.W

open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)

theorem cross (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    (θ : (n → ℂ) → ℂ)
    (hyp : ∀ F ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ)
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (w : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t t' : n → ℂ) :
    F (upd w b t) * θ t' = θ t * F (upd w b t') := by
  obtain ⟨a, ha⟩ := hyp _ (slice_th c L ΛM F hF w b)
  have e1 := congrFun ha t
  have e2 := congrFun ha t'
  simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
  rw [e1, e2]
  ring

theorem key (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    (θ : (n → ℂ) → ℂ)
    (hyp : ∀ F ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ)
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (t0 : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) :
    F z * θ t0 ^ s.card = (∏ b ∈ s, θ (part z b)) * F (repl t0 s z) := by
  induction s using Finset.induction_on generalizing z with
  | empty =>
    have hr : repl t0 ∅ z = z := by
      funext τ i j
      unfold repl
      simp
    rw [hr]
    simp
  | insert b s hb ih =>
    have hc := cross c L ΛM θ hyp F hF (repl t0 s z) b (part z b) t0
    have h1 : upd (repl t0 s z) b (part z b) = repl t0 s z := by
      funext τ i j
      by_cases h : (i, j) = b
      · subst h
        simp [upd, repl, part, hb]
      · simp [upd, h]
    have h2 : upd (repl t0 s z) b t0 = repl t0 (insert b s) z := by
      funext τ i j
      by_cases h : (i, j) = b
      · subst h
        simp [upd, repl]
      · simp [upd, repl, Finset.mem_insert, h]
    rw [h1, h2] at hc
    rw [Finset.card_insert_of_notMem hb, pow_succ, ← mul_assoc, ih z, Finset.prod_insert hb]
    linear_combination (∏ x ∈ s, θ (part z x)) * hc

end PI.KerTens.W
