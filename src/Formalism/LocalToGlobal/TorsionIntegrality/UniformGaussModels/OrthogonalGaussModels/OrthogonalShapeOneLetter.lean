import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.G (unitBall)

namespace ConjugatePartitionShape

theorem factors (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 ε s2 : MaximalUnramifiedExtension l) (h2 : (g2 : ℂ_[l]) = ι L.g₂) (h3 : (g3 : ℂ_[l]) = ι L.g₃)
    (hs2 : (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 L)) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1)
    (hD : ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1) (hε : ‖ε‖ = 1)
    (hθ : ∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1)
    (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) (hω2 : ω₀ / 2 ∉ L.lattice)
    (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N) (s : ℂ) (hs : (N : ℂ) * s ∈ L.lattice) :
    ∃ V : PowerSeries ℂ_[l], Formalism.L2.Th1.E.IntS V ∧
      (Formalism.DworkPowerSeriesWeights.mvExp (-(PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε))) : PowerSeries ℂ_[l]) * V =
        thetaOne l L ι (ε : ℂ_[l]) ω₀ s := by
  have hW : Formalism.L2.Th1.E.IntCurve (Formalism.L2.Th1.E.curveL l L ι) := by
    unfold Formalism.L2.Th1.E.curveL
    rw [← h2, ← h3]
    exact Formalism.L2.Th1.E.ScaledModelNorms.intCurve_short l hl _ _ hg2 hg3 hD
  exact Formalism.L2.Th1.E.joint_integrality l L ι (by omega) hW g2 g3 s2 ε h2 h3 hs2 hε hθ ω₀ hω hω2 s N hN hlN hs

theorem cc_ph (l : ℕ) [Fact l.Prime] (hl : 2 ≤ l) (g2 g3 s2 ε : MaximalUnramifiedExtension l) :
    PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension l).subtype (phFF l g2 g3 s2 ε)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF hl, map_zero]

end ConjugatePartitionShape

open ConjugatePartitionShape

end Formalism.L2.Th1.Top
