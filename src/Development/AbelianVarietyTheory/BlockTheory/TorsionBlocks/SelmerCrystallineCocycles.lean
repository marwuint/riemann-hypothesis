import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.Statement
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WeaklyAdmissibleFiltrations.Statement
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open scoped ENNReal Matrix

section Rep

variable {Γ A : Type} [Group Γ] [CommRing A] {m : ℕ}

def twist (ρ : Γ →* GL (Fin m) A) (χ : Γ →* Aˣ) : Γ →* GL (Fin m) A where
  toFun g := Matrix.GeneralLinearGroup.scalar (Fin m) (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    have hc : ρ g * Matrix.GeneralLinearGroup.scalar (Fin m) (χ h) =
        Matrix.GeneralLinearGroup.scalar (Fin m) (χ h) * ρ g := by
      apply Units.ext
      exact ((Matrix.scalar_commute ((χ h : Aˣ) : A) (fun _ => Commute.all _ _)
        ((ρ g : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)).eq).symm
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (ρ g), hc]
    simp only [mul_assoc]

end Rep

section BK

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

def IsCrysCocycle (T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀) (f : ↥Gw → Fin m → O₀) : Prop :=
  (fun (g : ↥(Loc.GK Bw.Kw)) (j : Fin m) => Bw.toLL (f (Bw.e.symm g) j)) ∈
    Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (P.PD Bw.Kw) (Bw.rep (T.comp Gw.subtype))

variable {O' : Type} [CommRing O'] [IsDomain O'] (ι : O₀ →+* O')

end BK

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1

section HidaSetting

variable (D : D7) (i : D.ntw.Tw)

abbrev GE : Type := G D.host.E D.nd.Om

abbrev decAt (v : PlE D.host) : Subgroup (GE D) := Dec (F := D.host.E) (D.nd.plOm.1 v)

def chiOf (s : D.ntw.Sig i) : GE D →* (D.ntw.O0 i)ˣ :=
  D.ntw.chi1 i (D.ntw.jS i s) (D.ntw.side i s)

def latT (s : D.ntw.Sig i) : GE D →* GL (Fin D.R.r) (D.ntw.O0 i) :=
  twist (D.ntw.rhoS i s) (chiOf D i s)⁻¹

end HidaSetting

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
