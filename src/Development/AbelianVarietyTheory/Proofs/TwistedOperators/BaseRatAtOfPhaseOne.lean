import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormsBasisInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvaluatesOfUnif
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupLevelActionEqInvSmulTranslate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Arith Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRatObj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

end GlobalTheory.LiftRatObj

end
