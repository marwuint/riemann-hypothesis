import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AHodgeDgalHodgeOfCgTrueG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SepConjG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TmRankOne

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
theorem _root_.UpperTheory.GalS.ghOf'_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : _root_.UpperTheory.GalS.CuspUAlt) (hB : GlobalTheory.Published.DeRhamPotSemistable) (hGL : _root_.UpperTheory.GalS.CarUAlt)
    (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T) (hl : LabTrue D T) : UpperTheory.GalS.GalHodgeN D T :=
  ⟨(_root_.GlobalTheory.HodgeOfTrue.galHodge0_of_cgTrue trivial) hL hF hG hB hGL C, _root_.GlobalTheory.WildFull.main D T hl, fun π hc _ _ hw k => (_root_.UpperTheory.GalS.sep_conj_g_alt trivial) hL hF C π hc hw k,
    fun _ S π w ht => _root_.UpperTheory.GalS.tm_rankOne_alt hL C S π w ht⟩
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
end GlobalTheory.GalAway
end
end
