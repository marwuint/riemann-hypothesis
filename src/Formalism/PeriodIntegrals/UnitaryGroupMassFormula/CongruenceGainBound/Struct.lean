import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

abbrev UV (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × Fin Sh.r1

abbrev AV (Sh : Shape) : Type := Sh.ZV ⊕ UV Sh

abbrev ETI (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × ℕ × Fin 4

def zt (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (v : Fin Sh.nV) (sg : Fin (Sh.n' v)) (k : ℕ)
    (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.X (Sum.inl ⟨v, (sg, a, b)⟩) ^ (p ^ k)

def ut (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV)
    (sg : Fin (Sh.n' v)) (k : ℕ) (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  if sg ∈ TT v then
    MvPowerSeries.C (MvPolynomial.X (⟨v, (sg, 0, a)⟩ : Sh.FrV) ^ (p ^ k)) * MvPowerSeries.X (Sum.inr ⟨v, (sg, b)⟩) ^ (p ^ k)
  else 0

end PI.UnitaryGroupMassFormula.PadicGainBound
