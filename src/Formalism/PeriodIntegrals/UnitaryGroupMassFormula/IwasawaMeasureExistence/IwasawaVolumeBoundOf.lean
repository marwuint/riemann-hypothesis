import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicFundamentalDomain

noncomputable section

namespace PI.IwaMeasEx.KV

open MeasureTheory
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
  Formalism.L2.S.S7.PositiveOrthantChangeOfVariables
open Formalism.HermitianLatticeCounting.S7 (dimN Vsph)
open PI.IwaMeasEx.Sk

structure admitted {X : CData} {J : ℕ} (c : Composition J) (D : BaseDatum X.I J) where
  μK : Measure X.I.GA
  μN : Measure X.I.GA
  μM : Measure X.I.GA
  cIw : ℝ≥0∞
  FN : Set X.I.GA
  FM : Set X.I.GA
  Om : Set X.I.GA
  VM : ℝ≥0∞
  hK : PK D μK
  hN : PN D c μN
  hM : PM D c μM
  hI : IntF μK (muP D c μN μM) cIw
  hF : FdP D c μN μM FN FM Om
  hL : LeviP D c μM FM VM

structure Sc where
  s : ℝ≥0∞
  sN : ℝ≥0∞
  sM : ℝ≥0∞
  vU0 : ℝ

end PI.IwaMeasEx.KV

end
