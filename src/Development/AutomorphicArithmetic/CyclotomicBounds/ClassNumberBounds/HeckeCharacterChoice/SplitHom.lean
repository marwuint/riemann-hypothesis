import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitDef

open NumberField

namespace KStar.Choice

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {p : ℕ}

private theorem ker_isPrime {R : Type*} [CommRing R] (hp : p.Prime) (f : R →+* ZMod p) :
    (RingHom.ker f).IsPrime := by
  have := Fact.mk hp
  exact RingHom.ker_isPrime f

end KStar.Choice
