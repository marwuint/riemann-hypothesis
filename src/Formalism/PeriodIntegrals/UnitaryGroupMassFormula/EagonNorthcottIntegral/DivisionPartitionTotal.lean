import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

def NoX {D : ℕ} (f : P D) : Prop := f ∈ Set.range (rename Sum.inr : S D → P D)

def IsCyc {D : ℕ} (a j : ℕ) (ω : W D) : Prop := Gr a j ω ∧ K ys ω = 0

def IsZL {D : ℕ} (a j : ℕ) (ω : W D) : Prop := IsCyc a j ω ∧ ∀ J, NoX (ω J)

end PI.EagonNorthcottZ
