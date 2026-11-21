import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.HeckeIntertwinersInert
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

open Formalism.BasicNotions IsDedekindDomain NumberField

noncomputable section
namespace GlobalTheory.InertOfConj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

end GlobalTheory.InertOfConj
