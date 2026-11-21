import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosed

set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefEig

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem actLev_levB (p : PtAt ex Csz) (i : Fin D.R.m) :
    ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  exact ⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩

set_option maxHeartbeats 1000000 in

theorem mem_eigSub_iff (p : PtAt ex Csz) (i : Fin D.R.m) (χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (f : p.T.R ((i : ℕ) + 1)) :
    f ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      ∀ u : (p.F.lv2.lvl false).P,
        actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f := by
  simp only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  rfl

end GlobalTheory.DefEig
