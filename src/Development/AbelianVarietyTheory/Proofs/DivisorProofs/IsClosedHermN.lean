import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResAniso

variable (D : D7) (n : ℕ)

def hermN : AddSubgroup (Mx D n n) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    change adj _ = _ at ha hb ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [map_add, h1, h2]
  zero_mem' := by simp [adj]
  neg_mem' := by
    intro a ha
    change adj _ = _ at ha ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at h1 ⊢
    rw [map_neg, h1]

variable {D n}

variable (D n)

variable {D n}

end GlobalTheory.ResAniso
end
