import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.PrincLevelSub

private lemma ext1_bot_one_apply {G : Type} [Group G] (x : G) :
    Formalism.L2.DIV.ext1 (⊥ : Subgroup G) (⇑(1 : (⊥ : Subgroup G) →* ℂˣ)) x = 1 := by
  unfold Formalism.L2.DIV.ext1
  split <;> rfl

theorem levChi_triv {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i)) :
    Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  simp [Lev.levChi, Formalism.L2.DIV.levFn, LevCh.datWp, LevCh.triv, Lev.datY, Formalism.L2.DIV.LevelP.triv,
    ext1_bot_one_apply]
  exact ext1_bot_one_apply _

end GlobalTheory.HolRead.PrincLevelSub
