import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Objects

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

structure IsDiscreteSelfDualSum (A : NAut N) (P : List (Part A.CG)) : Prop where

  discrete : ∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d

  selfDual : ∀ p ∈ P, A.csd p.π

  distinct : P.Nodup

structure IsBaseChange (B : NBC A) (j : ℕ) (π : B.AU j) (P : List (Part A.CG)) : Prop where

  parts : IsDiscreteSelfDualSum A P

  rank : rankIso N A P = R.nV

  split : ∀ w : PlE H, IsSplitPl H w → isoLoc N A P w = B.locAU j π w

  inertUnr : ∀ w : PlE H, ¬ IsSplitPl H w → A.unr (isoLoc N A P w)

  inertSat : ∀ w : PlE H, ¬ IsSplitPl H w →
    A.frobEig (isoLoc N A P w) = ubc R.nV (B.satAU j π w)

  infChar : ∀ τ : H.E →+* ℂ, isoInf N A P τ = B.infW j (B.wtAU j π) τ

end Objects

end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

end
