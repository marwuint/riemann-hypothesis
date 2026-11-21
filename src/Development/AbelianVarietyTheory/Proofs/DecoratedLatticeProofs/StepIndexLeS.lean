import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u} {t : W.P.T}

theorem step_index_le_s (J : QJ a t) (i : Fin J.r) {j : ℕ} (hj : j + 2 ≤ B.R.m) : j ≤ (J.G i).s := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  omega

def phi (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ ((J.G i).FX j (by have := step_index_le_s J i hj; omega))

def H (J : QJ a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) (i : Fin J.r) :
    Subgroup (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
  prX (Cgrp (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev j ((J.G i).s - j + 1) (by have := step_index_le_s J i hj; omega)).J
    ((J.E i).rep j ((J.G i).s - j) (Nat.add_sub_cancel' (step_index_le_s J i hj)) (α i)))

end GlobalTheory.LevProd
end
