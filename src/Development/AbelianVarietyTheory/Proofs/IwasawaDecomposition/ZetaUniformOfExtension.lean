import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  have key : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (R.toCx3 F).zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (R.toCx3 F).zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j h1 h2
    subst h1
    cases h2
    exact C.pt
  exact ⟨⟨C.wU, C.bij, C.eNu, C.NuC, C.nu, key Y₁.tup Y₁.jA h1 h2⟩⟩

end GlobalTheory.Mem.R3

