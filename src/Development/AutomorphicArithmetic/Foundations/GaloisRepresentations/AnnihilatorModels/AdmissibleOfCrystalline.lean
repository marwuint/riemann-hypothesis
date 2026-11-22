import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale

noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per

namespace UpperTheory.Gal.crystallineComparison

def AffFinProj : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f → AffFin Y

theorem heckePol_map {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (q n : ℕ) (θ : ℕ → K) :
    (heckePol q n θ).map f = heckePol q n fun j => f (θ j) := by
  simp [heckePol, Polynomial.map_sum]

def AdmOfCrys : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → admitted (σCr P K) (finrank ℚ_[l] ↥(K0 K)) ρ

theorem admissible_of_crystalline : AdmOfCrys := by
  intro l _ P K V _ _ ρ h
  have e : Dinv (σCr P K) ρ = Dcris (P.PD K) ρ := by
    unfold Dinv Dcris actVB σCr
    refine iInf_congr fun g => ?_
    congr 3
    ext b
    simp [P.PD_actB]
  unfold admitted
  rw [e]
  exact h

end UpperTheory.Gal.crystallineComparison
