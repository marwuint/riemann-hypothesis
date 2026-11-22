import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BasePairChar

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem unrAt_of_unramAt {c : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hc : GlobalTheory.WeilParts.UnramAt ε c) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w.under (𝓞 D.host.F) = v) : GlobalTheory.LFun.UnrAt c w := by
  subst hw
  have key : ∀ y, Formalism.L2.Host.IsUnitAt w y → finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ) ∈ intAE D := fun y hy =>
    (GlobalTheory.LFun.mem_int_iff _).2 fun P => by
      rw [show GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (GlobalTheory.LFun.locIdele D.host.F w y : (AE D)ˣ)) =
        Neutral.B1.finiteSingle _ w y from GlobalTheory.LFun.finTens_locIdele w y]
      by_cases e : P = w
      · subst e; rw [GlobalTheory.LFun.finSingle_self]; exact hy.le
      · rw [GlobalTheory.LFun.finSingle_ne e, map_one]
  obtain ⟨α, rfl, h1, -⟩ := hε
  intro y hy
  have hs : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * ((GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1) =
      (GlobalTheory.LFun.locIdele D.host.F w y : AE D) - 1 := by
    refine GlobalTheory.LFun.tens_ext ?_ ?_
    · simp only [map_mul, map_sub, map_one, GlobalTheory.LFun.infTens_locIdele, sub_self, mul_zero]
    · apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      have e2 := GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y
      refine FiniteAdeleRing.ext _ fun P => ?_
      simp only [map_mul, map_sub, map_one, e2]
      have hA : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (GlobalTheory.LFun.finTens D.host.F D.host.E
          (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) =
          GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl
      rw [hA]
      change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (α ⊗ₜ[D.host.F] (1 : D.host.E)) P *
          (Neutral.B1.finiteSingle D.host.E w y P - 1) = Neutral.B1.finiteSingle D.host.E w y P - 1
      rw [GlobalTheory.LFun.finAdEquiv_tmul, map_one, mul_one]
      by_cases hP : P = w
      · subst hP
        rw [GlobalTheory.LFun.finSingle_self]
        have : α (P.under (𝓞 D.host.F)) = 1 := h1
        rw [this, map_one, one_mul]
      · rw [GlobalTheory.LFun.finSingle_ne hP, sub_self, mul_zero]
  have h := hc _ hs (key y hy) (by
    rw [← map_inv]
    refine key _ ?_
    unfold Formalism.L2.Host.IsUnitAt at hy ⊢
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  exact (congrArg Circle.toUnits h).trans (map_one _)

end GlobalTheory.BasePairChar
