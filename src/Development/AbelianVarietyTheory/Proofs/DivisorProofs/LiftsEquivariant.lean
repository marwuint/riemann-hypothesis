import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum

noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem postOn_gaL {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (x : MMap M) :
    postOn M (gaL V β L eG c) x = ∑ g, c g • postOn M (actL V β L (eG g)) x := by
  ext v h
  simp [postOn, gaL, LinearMap.sum_apply, Finset.sum_apply]

variable {R} {F : Face D A}

end Record

end GlobalTheory.AdjBlock

end
