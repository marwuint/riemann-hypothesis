import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HeckeReadTie : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt T R i σ hV (κ i)

end GlobalTheory.HeckeSupSt
