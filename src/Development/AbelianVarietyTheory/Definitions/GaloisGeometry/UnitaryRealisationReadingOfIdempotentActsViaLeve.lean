import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AdmissiblePeriodOfPeriodInt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HypOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite

noncomputable section

namespace GlobalTheory.NRows.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

section Read
variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
  (X : GlobalTheory.NJoin.RealAt D cf nch tp)

theorem exists_vec {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) :
    ∃ y, X.R.extV j (X.tupT μ) y = X.fn hμ j f := (X.IL.jMt μ hμ j f).2.1

end Read

theorem unitaryRealisationReading_of_idempotent_acts_via_levelGroup {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (h : ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1))
      (l : (X.R.cV j).W →ₗ[ℂ] ℂ),
      Formalism.IndefR.Links.gaL (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.datVt j (X.tupT μ)) X.R.eG
        (Formalism.IndefR.Links.RealDat.eC (A := X.A) (Formalism.IndefR.Links.sg0 D X.A)) (fun g => l (X.fn hμ j f g)) =
        fun g => l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g)) : GoodIdempotentReadsAsGoodTypeProjector X := by
  intro μ hμ j f y hy
  unfold GlobalTheory.DownLift.GoodVt
  rw [hy]
  constructor
  · intro hf l
    rw [h μ hμ j f l, hf]
  · intro hg
    apply (X.IL.jMt μ hμ j).injective
    apply Subtype.ext
    funext g
    have key : ∀ l : (X.R.cV j).W →ₗ[ℂ] ℂ,
        l (X.fn hμ j (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f) g - X.fn hμ j f g) = 0 := fun l => by
      rw [map_sub, sub_eq_zero]
      exact congrFun ((h μ hμ j f l).symm.trans (hg l)) g
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (V := (X.R.cV j).W) _).1 key)

end GlobalTheory.NRows.Model

end
