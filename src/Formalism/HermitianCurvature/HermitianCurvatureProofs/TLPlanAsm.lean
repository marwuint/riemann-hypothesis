import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Formalism.FourierDecayAlt.TL
