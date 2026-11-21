import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompleteOfCompactBalls
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDieudonne

namespace GlobalTheory.CovTop

structure Hypotheses2 : Prop where

  p1 : GlobalTheory.Published.ToroidalCompactification

  p2 : GlobalTheory.Published.VolGe

  p3 : GlobalTheory.Published.VolNef

  p4 : GlobalTheory.Published.ArCalc

  p5 : GlobalTheory.Published.AbelianDeRham

  p6 : GlobalTheory.Published.TamagawaSpecialUnitary

  p8 : GlobalTheory.Published.RayClassFieldSt

  p12 : GlobalTheory.Published.SemistableReductionSt

  p13 : GlobalTheory.Published.StrongApproxSU

  p14 : GlobalTheory.Published.GreenSeriesSt

  p16 : GlobalTheory.Published.GoodChernWeil

  p19 : GlobalTheory.Published.LandherrSt

  p20 : GlobalTheory.Published.HasseNormSt

  p22 : GlobalTheory.Published.SemiAbelianHomExtension

  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove

  p25 : GlobalTheory.Published.principalPolarisationOneSection

  p26 : GlobalTheory.Published.AbMulNSt

  q1 : GlobalTheory.Published.GrothendieckMessing

  q3 : GlobalTheory.Published.DeRhamCanonicalExtension

  q4 : GlobalTheory.Published.PrismaticDieudonneHodge

  q6 : GlobalTheory.Published.KawamataViehweg

  q7 : GlobalTheory.Published.NefNumerics

  q8 : GlobalTheory.Published.L2ExtensionLogCanonical

  q9 : GlobalTheory.Published.ArithHilbertSamuel

  q10 : GlobalTheory.Published.ChowFormExists

  q11 : GlobalTheory.Published.CycleHeights

  q13 : GlobalTheory.Published.SerreHolomorphicSections

  q15 : GlobalTheory.Published.NadelVanishingAndNonKltDivisor

  q16 : GlobalTheory.Published.Principalisation

  q18 : GlobalTheory.Published.FormalAlgebraisation

end GlobalTheory.CovTop
