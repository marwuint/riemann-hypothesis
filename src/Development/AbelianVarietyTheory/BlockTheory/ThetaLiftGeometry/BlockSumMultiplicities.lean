import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW

variable (D : D7)

def UnramIn (p : ℕ) : Prop :=
  ∀ v ∈ placesOver D.host.E p, Algebra.IsUnramifiedAt ℤ v.asIdeal

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

abbrev locRep {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Representation (Br.LL D.nbr i w hw) (Br.G D.nbr i w hw) (Fin k → Br.LL D.nbr i w hw) :=
  matRep (Br.loc D.nbr i w hw M)

def CrysAt {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M)

def mult {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (τ : Emb D i w hw) (a : ℤ) : ℤ :=
  multV (Br.PD D.loc D.nbr i w hw) (locRep D i w hw M) τ a

end Place

variable {D}

variable (D)

end GlobalTheory.IndefiniteRowSideFullHecke.BlockSumMultiplicities
