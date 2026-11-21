import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

section Param

variable {R : Ranks}

def run (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Multiset.range R.t).map fun k : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - ((k : ℚ) + 1)

def param (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

def sgnOf (ep b : Bool) : ℚ := if ep = b then 1 else -1

end Param

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOver (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then
    (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp (D.host.conj : D.host.E →+* D.host.E)
  else D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def PP (i : D.nd.Loc) (ρ : D.what₂.Tau) : Multiset ℚ := param (D.hc ρ) (liftIdx D i)

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Units.map (Matrix.scalar (Fin 1) : D.nd.O i →+* Matrix (Fin 1) (Fin 1) (D.nd.O i)).toMonoidHom).comp
    (D.nd.chi i c)

def WeightParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infWt i (embOver D ρ false) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) ∧
    D.naut.infWt i (embOver D ρ true) = (PP D i ρ).map (fun p => ((-(p - 1 / 2) : ℚ) : ℂ))

def BlockCharParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ false) =
      {((-(D.hc ρ).e (liftIdx D i) - 1 / 2 : ℚ) : ℂ)} ∧
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ true) =
      {(((D.hc ρ).e (liftIdx D i) + 1 / 2 : ℚ) : ℂ)}

end GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

end
