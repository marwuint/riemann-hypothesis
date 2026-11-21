import Formalism.SharpRestriction.FamCore
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
import Formalism.ZetaNonvanishing.ZetaLandau

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

theorem An.logDerivative_at_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : An.logDerivativeAtOne χ = GlobalTheoryTheory.logDerivativeAtOne χ := rfl

def EAt (Λ : Level) (D : D7) (x eps C : ℝ) : Prop := EAtH Λ D.host.toHostRaw D.host.TT x eps C

def EFamC (Λ : Level) {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EAt Λ (Fm.D x i) x eps C

end Formalism.HC

end
