import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt

set_option genSizeOfSpec false
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)

structure QLev {v : VCom f.c} {t : W.P.T} (F : GlobalTheory.QPl.QFam v (f.t t)) : Prop where
  places : ∃ pl : Fin F.r ≃ (pk W).Q t, ∀ i, Formalism.L2.NTheta.IsIdemAt (F.Q i).q.e (pl i).1 ∧ (F.Q i).q.v = (pl i).1.under (𝓞 D.host.F)
  mid : ∀ i j d hd, j < D.R.m → ∀ x ∈ KO (F.Q i).k _,
    ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j ∈ levS _ ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ ((F.Q i).T.lev j d hd).J) ∧
    ∀ hx : x ∈ ((F.Q i).T.lev j d hd).J, levChi _ ((pk W).βY j) ((pk W).datYt t j (lvP W))
      ((f.g.b j)⁻¹ * (F.Q i).gl j d hd x * f.g.b j) = (((F.Q i).T.lev j d hd).lam ⟨x, hx⟩ : ℂ)
  top : ∀ i, ∀ x ∈ KO (F.Q i).k _, ∀ g, (ofSplit (F.Q i).q).IsLoc (F.Q i).FT g x →
    (f.g.bT⁻¹ * g * f.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ (F.Q i).T.levTop.J)

end GlobalTheory.Fam

end
