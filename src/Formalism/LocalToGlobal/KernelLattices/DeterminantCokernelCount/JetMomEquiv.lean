import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomEq

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.Ker.I3.JetMomA

section Clauses

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

def TranslateJetMomentLawAnyIdempotentLevel : Prop :=
  ∀ (n m : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam m ε → 2 * n ≤ m → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (k : ℕ) (y : Fin k → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) (B.eNat χ N N' L L'))) = μ g

end Clauses

section Zero

variable {D : D7} {q : ℕ} [Fact q.Prime]

theorem wPh_of_int (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    wPh D T q x = Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) := by
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T x : ℂ)) = (-1 : ℂ) ^ m := by
    rw [h, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold wPh
  split_ifs with hq
  · rfl
  · rw [hE]
    have hex : ∃ s : ℂ, ∃ (k : ℕ) (m' : ℤ), (q : ℝ) ^ k * qH D T x = (m' : ℝ) ∧ s = (-1 : ℂ) ^ m' :=
      ⟨(-1 : ℂ) ^ m, 0, m, by rw [h]; simp, rfl⟩
    obtain ⟨k, m', hm', hs⟩ := Classical.epsilon_spec hex
    rw [hs]
    rw [h] at hm'
    have hm'' : m' = (q : ℤ) ^ k * m := by exact_mod_cast hm'.symm
    have hodd : Odd ((q : ℤ) ^ k) := by
      have := ((Fact.out : q.Prime).odd_of_ne_two hq).pow (n := k)
      exact_mod_cast this
    rw [hm'', zpow_mul, hodd.neg_one_zpow]

end Zero

section Merged

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {q : ℕ} [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q]) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)
  (G : VC D N N' → ℂ)

def FirstMomentVectorLaw : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) G)) = μ g

end Merged

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q]) (Ω : ℂ_[q])

theorem firstMomentVectorLaw_iff {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r) :
    FirstMomentVectorLaw B lam Ω b μ (B.eNat χ N N' L L') ↔ TranslateJetMomentLaw B χ lam Ω L L' b μ := Iff.rfl

end Formalism.L2.Ker.I3.JetMomEq
