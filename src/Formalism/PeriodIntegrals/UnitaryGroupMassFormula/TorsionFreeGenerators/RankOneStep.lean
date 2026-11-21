import Mathlib

namespace PI.FGTFG

def ProjStep : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [NoZeroSMulDivisors R M], Module.Projective R M

end PI.FGTFG
