import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.UrRing
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocH

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

namespace TwB

section Settings

variable (F : Type) [Field F] [NumberField F]

abbrev TwT : Type :=
  Σ l : Nat.Primes, {w : HeightOneSpectrum (𝓞 F) // (((l : ℕ) : ℕ) : 𝓞 F) ∈ w.asIdeal}

instance (i : TwT F) : Fact ((i.1 : ℕ)).Prime := ⟨i.1.2⟩

end Settings

section OneLL

variable {l : ℕ} [hl : Fact l.Prime] {F : Type} [Field F] (LL : FinExt l) (φ : F →+* PadicAlgCl l)
  (hφ : ∀ x, φ x ∈ LL.1)

def phiL : F →+* ↥LL.1 := φ.codRestrict LL.1.toSubfield hφ

def embF : F →+* FractionRing ↥(OL LL) := (toFrac LL).comp (phiL LL φ hφ)

end OneLL

end TwB

end Formalism.BasicNotions.Examples₂
