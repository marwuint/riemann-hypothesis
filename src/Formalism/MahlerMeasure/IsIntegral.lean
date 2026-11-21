import Formalism.MahlerMeasure.GoodCount

namespace Formalism.GM.M

open MvPolynomial Finset

def IsIntegral' {σ : Type} (p : ℕ) [Fact p.Prime] (u : MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ m, ‖u.coeff m‖ ≤ 1

def PhiInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ), Function.Injective w → Function.Injective e →
    (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n z : ℕ) (u : MvPolynomial σ ℚ_[p]), IsIntegral' p u →
      IsIntegral' p (((p : ℚ_[p]) ^ ((r + 1) * (Nat.log p (o + n + r + z) + 1))) • Formalism.GM.tiePhi w e o n z u)

end Formalism.GM.M
