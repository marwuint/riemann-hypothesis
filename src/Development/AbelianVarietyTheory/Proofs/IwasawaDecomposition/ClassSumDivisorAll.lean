import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RayClassFieldsInCoefficientFieldConstructedPoint
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SideWeightRaysOfRayRec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPoint
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmallFrameAtColumn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SeriesUpdatePreservesParamFreeConditionsRayField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LargeBaseRayCondition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreSlotRX
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoTies

theorem twAllAt_tr {D : D7} (N : ∀ u, Submodule (NumberField.RingOfIntegers D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    {x : NChoice D} {y : ThData D} (H : DQ.TwAllAt D x y) : DQ.TwAllAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, fun a ha => ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2 a ha
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

theorem twAll_pt {K : Ctx} (β : BPt K) : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAllAt_tr (nPrime β.p.L) β.p.ht β.twAll

end GlobalTheory.GeoTies
