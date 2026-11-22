import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RallisConvOfHypotheses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NonGaloisDownLiftNonvanishing

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
namespace GlobalTheory.DownLift.AtReal
theorem lift_splits_locally : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D)
    (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  intro hP hH hX D cf nch tp X j t
  have hR : GlobalTheory.RawLift.RallisConv D := GlobalTheory.RawLift.Assembled.rallisConv_of_siegelWeil hP hX.sw D
  have hN : ∀ i t, GlobalTheory.DownLift.NonVan X.R i t := fun i t =>
    _root_.GlobalTheory.T.nonGalois_downLift_nonvanishing hP hX.dbl hX.udbl hX.hl hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full i t
  exact ((_root_.GlobalTheory.DownLift.liftRows_injective_and_typeProperties_of_nonvanishing hP hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full hR hN).2 j t).1
end GlobalTheory.DownLift.AtReal
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRep_descends_at_real_places : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  first | exact @_root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | exact _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | (intros; apply _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally <;> assumption)
end
