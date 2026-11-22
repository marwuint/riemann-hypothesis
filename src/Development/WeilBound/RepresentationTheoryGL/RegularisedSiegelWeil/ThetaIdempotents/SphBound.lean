import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentity
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleReality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := _root_.GlobalTheory.CompanionTheory.JacobiMaps.mapsExist
theorem htExist : HtExist := _root_.GlobalTheory.CompanionTheory.HtEx.htExist
theorem heckeEta : HeckeEta := _root_.GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta
theorem fjEis : FJEis := _root_.GlobalTheory.CompanionTheory.FJE.fjEis _root_.GlobalTheory.CompanionTheory.ZUnf.zUnfold _root_.GlobalTheory.CompanionTheory.ThTw.thTwist
theorem pcBound : PcBound := _root_.GlobalTheory.CompanionTheory.PcB.pcBound
theorem rSec : RSec := _root_.GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist htExist
theorem eisHol : EisHol := _root_.GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist htExist
theorem thTotal : ThTotal := _root_.GlobalTheory.CompanionTheory.ThTot.thTotal heckeEta
theorem cfFJ : CfFJ := _root_.GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound pcBound
theorem pcFc : PcFc := _root_.GlobalTheory.CompanionTheory.PcFc.target mapsExist _root_.GlobalTheory.CompanionTheory.FourierN.fourierZero
theorem sphBound : SphBound := _root_.GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist htExist
theorem resMu : ResMu :=
  _root_.GlobalTheory.CompanionTheory.ResMu.resMu_main mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound _root_.GlobalTheory.CompanionTheory.FourierN.fourierZero _root_.GlobalTheory.CompanionTheory.SWCoef.coefDataExists
theorem polar : Polar :=
  _root_.GlobalTheory.CompanionTheory.RswPolar.polar mapsExist htExist heckeEta _root_.GlobalTheory.CompanionTheory.Dblock.rightId _root_.GlobalTheory.CompanionTheory.PoleBound.poleReal fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
