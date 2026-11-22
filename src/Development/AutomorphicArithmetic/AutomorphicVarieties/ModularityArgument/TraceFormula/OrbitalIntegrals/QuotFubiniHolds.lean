import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

namespace UpperTheory.V.Z.Tf.Orb

theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

theorem gLTop_holds : GLTop := UpperTheory.V.Z.Tf.Orb.gLTop

theorem extCont_holds : ExtCont := UpperTheory.V.Z.Tf.Orb.extCont

theorem centComm_holds : CentComm := UpperTheory.V.Z.Tf.Orb.centComm

theorem twCent_holds : TwCent := twCent_of

theorem haarComm_holds : HaarComm := UpperTheory.V.Z.Tf.Orb.haarComm

theorem quotIndep_holds : QuotIndep := UpperTheory.V.Z.Tf.Orb.quotIndep

theorem normEx_holds : NormEx := UpperTheory.V.Z.Tf.Orb.normEx

theorem quotInt_holds : QuotInt := quotInt_of

theorem untwist_holds : Untwist := UpperTheory.V.Z.Tf.Orb.untwist

theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
