import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An.Det

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ}

section Jet

variable {n : ℕ} (J : JetRing ℂ I n)

def HasJet (f : (I → ℂ) → ℂ) (b : J.B) : Prop := AnalyticAt ℂ f 0 ∧ jet J f = b

variable {J}

theorem HasJet.mul (hC : JetCalc) {f g : (I → ℂ) → ℂ} {a b : J.B} (h : HasJet J f a) (k : HasJet J g b) :
    HasJet J (fun z ↦ f z * g z) (a * b) :=
  ⟨h.1.mul k.1, h.2 ▸ k.2 ▸ ((hC I n J).2.1 f g h.1 k.1).1⟩

theorem HasJet.add (hC : JetCalc) {f g : (I → ℂ) → ℂ} {a b : J.B} (h : HasJet J f a) (k : HasJet J g b) :
    HasJet J (fun z ↦ f z + g z) (a + b) :=
  ⟨h.1.add k.1, h.2 ▸ k.2 ▸ ((hC I n J).2.1 f g h.1 k.1).2⟩

end Jet

end GlobalTheory.LatJet.An.Det
