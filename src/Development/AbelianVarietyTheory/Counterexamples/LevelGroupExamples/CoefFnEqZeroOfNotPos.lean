import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArithmeticGroupCuspCentreLattice
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsTie
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotJInjRdOfConst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement
import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

noncomputable section

namespace GlobalTheory.ReadingTieCheck

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt MeasureTheory GlobalTheory.TorusFourier GlobalTheory.MaxCuspKilled

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

theorem reading_mem_SS (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k) :=
  readings_holomorphic_cuspForms siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, cutR_le T.C j u F.2⟩ k

theorem tieRead_iff : TieReadSt h j ↔ ∀ u : WeightFamilies.Wt D j, JInjRd T j (wtA u) u.n :=
  ⟨fun H => H.2, fun H => ⟨reading_mem_SS h j, H⟩⟩

theorem tieRead_holds (hj : InR D j) : TieReadSt h j :=
  (tieRead_iff h j).2 fun u =>
    GlobalTheory.ReadingIndependence.jInjRd_of_laws T h.toLawsCore.toLawsM hj (wtA u) u.n

end Record

end GlobalTheory.ReadingTieCheck
