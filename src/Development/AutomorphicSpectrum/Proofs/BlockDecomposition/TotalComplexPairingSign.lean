import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.TotPairing

variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} {M : DCx.{w''} R}

def cmp (K : DCx.{w} R) (p q : ℕ) : (∀ a b, K.X a b) →ₗ[R] K.X p q :=
  (LinearMap.proj (R := R) (φ := fun b => K.X p b) q).comp
    (LinearMap.proj (R := R) (φ := fun a => ∀ b, K.X a b) p)

theorem cmp_apply (K : DCx.{w} R) (p q : ℕ) (x : ∀ a b, K.X a b) : cmp K p q x = x p q := rfl

end GlobalTheory.CompanionTheory.TotPairing
