import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu

noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def coPtSb (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d a b : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) b s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a (d * b) s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) *
        GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) (d * b) s

end GlobalTheory.LambdaValuationPowers
