import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Section
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]

def BcrisPlus.liftFracWitt (g : WittVector p k →+* R) :
    FractionRing (WittVector p k) →+* BcrisPlus p R :=
  fracWittLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp
    ((algebraMap (Ainf p R) (Acris p R)).comp (Ainf.liftWitt p g))) (BcrisPlus.isUnit_p p R)

variable {p}

@[simp] theorem BcrisPlus.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    BcrisPlus.liftFracWitt p g (algebraMap _ _ a) =
      algebraMap (Acris p R) _ (algebraMap (Ainf p R) _ (Ainf.liftWitt p g a)) :=
  fracWittLift_algebraMap p _ _ a

end Reformulated.AutPerF
