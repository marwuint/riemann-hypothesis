import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Definitions.Divisors.ConstantUniqueOfEqProduct
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

namespace GlobalTheory.SingleDatum.BasePair

variable {D : D7}

theorem placeIdem_mul_eq_zero {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hne : v' ≠ v) : ε' * ε = 0 := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  have e : α' * α = 0 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw; rw [h2' w hne.symm, zero_mul]
    · rw [h2 w hw, mul_zero]
  show pairA D.host.F 0 α' * pairA D.host.F 0 α = 0
  have e2 : pairA D.host.F 0 α' * pairA D.host.F 0 α = pairA D.host.F 0 (α' * α) := Prod.ext (mul_zero _) rfl
  rw [e2, e]
  rfl

end GlobalTheory.SingleDatum.BasePair

