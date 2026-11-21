import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CongL
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G1

def AuxiliaryInertOddPrime : Prop := ∀ d : ℕ, 0 < d → ∀ b : ℕ, ∃ (p : ℕ) (_ : Fact p.Prime), b < p ∧ IsSquare (-(d : ℚ_[p]))

def ArithK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ), 0 < d → ∀ x : E, x ^ 2 = -(d : E) →
  ∀ (τ₀ : E →+* ℂ) (Q : Finset ℕ), (∀ q ∈ Q, ∃ _ : Fact q.Prime, IsSquare (-(d : ℚ_[q]))) →
  ∃ A : Arith E, A.τ₀ = τ₀ ∧ (∃ f : ℚ, f ≠ 0 ∧ 2 * (A.ω : E) - (A.tr : E) = (f : E) * x) ∧
    (∀ (q : ℕ) [Fact q.Prime], IsSquare (-(d : ℚ_[q])) → A.SplitK q) ∧ ∀ q ∈ Q, A.Good q

def ScOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Even (Module.finrank ℚ (maximalRealSubfield E)) →
  ∀ (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p), Odd n → Sc S.D S.G

def RootAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (q : ℕ), q.Prime → A.SplitK q →
  ∀ w : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ w.asIdeal →
  ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal

end UpperTheory.Gal.G1
