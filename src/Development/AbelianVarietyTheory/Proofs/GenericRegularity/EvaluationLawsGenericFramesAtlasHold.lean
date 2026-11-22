import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem evLaws_genFr_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c ∧ IntDiagUnit Xo c ∧ GenFrEx Xo c ∧ ∀ h : GenFrEx Xo c, Atlas h := by
  intro E _ _ _ H Dw l Xo c
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨-, -, hwd, hwt, hint, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
  have hbc : FrBC Xo c := fun S T _ _ _ _ φ y =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
  exact ⟨⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c, hwt, hbc⟩, hint, genFrEx_of hT,
    _root_.GlobalTheory.Reg.atlas hT E H Dw l Xo c hbc⟩

end GlobalTheory.Reg
