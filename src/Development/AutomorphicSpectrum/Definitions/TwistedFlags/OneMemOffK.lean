import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Doubling (io hgt flat zetaA ZetaConvA IsMaj dblSp Khat HasIwasawa degPS)
open GlobalTheory.FinZeta (projV embV Kv Gv IsLocKer VacFin bddAut)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction (ofFr ipTh ptAt actSrc actTgt IsJoint UnitHighest kfin alS alT NodeGap)
open GlobalTheory.AdelicScalar (l2)
open scoped InnerProductSpace GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.CompanionTheory.Ipf.Loc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev FPl (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.F)

structure IsStep (k : Fin D.R.m) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) {PS PT : D.what₂.Tau → SPar} (M : DSModel S PS) (M' : DSModel T PT)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (Sb : Finset (FPl D)) (f₀ fF : WO S T → ℂ) : Prop where
  weil : IsWeilDatumO ψ S T χS χT om
  inf : IsInfFam θ
  parS : PS = parB (Ptw D) k
  parT : PT = parB (Ptw D) (k + 1)
  expo : ∀ τ, HasInfExp D χS τ (alS D k τ) ∧ HasInfExp D χT τ (alT D k τ)
  rank : T.rank = S.rank + D.R.t
  noQ : LS.Q = ∅
  places : ∀ v, v ∈ Sb ↔ ∃ PP ∈ LS.Pg, PP.under (𝓞 D.host.F) = v
  frameS : ∃ N : ℕ, Lev.IsBaseFrame S βS ΛS N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  frameT : ∃ N : ℕ, Lev.IsBaseFrame T βT ΛT N ∧ ∀ v : FPl D, (N : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ Sb
  vec : IsStepVecOf ψ θ S T (cart M) (cart M') ΛS ΛT βS βT LS χj ∅ (fun _ => 1) f₀ fF
  unr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sb → GlobalTheory.LFun.UnrAt χS w ∧ GlobalTheory.LFun.UnrAt χT w
  tame : ∀ PP ∈ LS.Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP χS (χj PP) (-1) ∧ Formalism.IndefR.Fin.TameAt e PP χT (χj PP) (-1)

end GlobalTheory.CompanionTheory.Ipf.Loc

end
