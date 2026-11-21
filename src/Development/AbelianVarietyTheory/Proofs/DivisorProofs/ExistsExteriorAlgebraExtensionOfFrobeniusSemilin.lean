import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobeniusTwistSmul

def FrobTw (K : Type) (p : ℕ) (W : Type) : Type := W

section
variable (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (W : Type) [AddCommGroup W] [Module K W]

instance : AddCommGroup (FrobTw K p W) := inferInstanceAs (AddCommGroup W)

instance : Module K (FrobTw K p W) := @Module.compHom K K W _ _ _ _ (frobenius K p)

end

end GlobalTheory.DI.FrobeniusTwistSmul
