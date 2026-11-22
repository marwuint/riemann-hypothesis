import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThmBGaussOrthOf
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.PairsK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NeZeroOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.IntegralOperatorTwoOrthogonal
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaAdditiveHomogeneousHomothety
import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.ThetaKappaShapeOfTransferIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OneLetterGaussTranslateOfCmCase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt

namespace Formalism.L2.Th1.Top

theorem calcC : CalcC := CalcC_proof
theorem cmDatum : CMDatum := CMDatum_proof
theorem jetsCM : JetsCM := JetsCM_of cmDatum
theorem calcP : CalcP := CalcP_of cmDatum
theorem kappa_integral : uniformGaussModelConditionReformulated := kappa_integral_of_calculation calcC
theorem hypShape : HypShape := HypShape_of calcC

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in

theorem modelInert (dK : ℕ) (L : PeriodPair) (hsq : Squarefree dK) (hmod : dK % 4 = 3)
    (hcm : Formalism.L2.Th1.CM.HasCMBy dK L) (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) (hd : ¬ l ∣ dK)
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) (ι : ℂ ≃+* ℂ_[l]) :
    ∃ g2 g3 ε : Formalism.L2.Th1.CM.MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 ∧ ‖ε‖ = 1 ∧
      ∀ n, ‖PowerSeries.coeff n (Formalism.L2.Th1.D.thetaS l g2 g3 ε)‖ ≤ 1 :=
  Formalism.L2.Th1.D.FAux.model l Formalism.L2.Th1.CM.cm2 Formalism.L2.Th1.CM.cm3 dK L hsq hmod hcm h5 hd hin ι

theorem ltNormExists : LTNormExists := lubin_tate_norm_exists
theorem transIntLT : TransIntLT := lubin_tate_transfer_integral
theorem local_kappa_shape_holds : uniformGaussModelConditionReformulated₂ := local_kappa_shape_of_transfer_integrality transIntLT
theorem theta_kappa_shape_holds : uniformGaussModelConditionEquivalent := theta_kappa_shape_of_transfer_integrality transIntLT
end Formalism.L2.Th1.Top
