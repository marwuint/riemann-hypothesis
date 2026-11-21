import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

end GlobalTheory.Fc.LabLinked
