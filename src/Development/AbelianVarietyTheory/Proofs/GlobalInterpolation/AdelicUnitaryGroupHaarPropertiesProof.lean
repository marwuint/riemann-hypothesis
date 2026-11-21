import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlac
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector

namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, _root_.GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite F E σ hσ M J hJ,
    _root_.GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele F E σ hσ M J hJ, _root_.GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, _root_.GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin F E σ hσ M J hJ⟩

end GlobalTheory
