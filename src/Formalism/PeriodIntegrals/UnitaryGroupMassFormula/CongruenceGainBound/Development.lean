import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.KernelEntryData

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

structure Counts (Sh : Shape) where
  ec : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r1 → ℕ
  ih : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℕ
  i0 : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin (Sh.n' v) → ℕ
  i2 : Fin Sh.nV → ℕ
  be : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r0 → Fin Sh.r1 → ℕ
  N : ℕ

def Counts.hits {Sh : Shape} (D : Counts Sh) (v : Fin Sh.nV) (s' : Fin (Sh.n' v)) : ℕ :=
  ∑ s, ∑ e ∈ range D.N, if posAdd s e = s' then D.ih v s e else 0

structure Counts.Ok (p : ℕ) {Sh : Shape} (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (D : Counts Sh) : Prop where
  ec_sum : ∀ v s, ((∑ b, D.ec v s b : ℕ) : ℤ) = al (TT v) (nu v) s
  ih_supp : ∀ v s e, D.ih v s e ≠ 0 → s ∈ TT v ∧ Odd e ∧ e < D.N
  h1 : ∀ v s e, (D.ih v s e : ℤ) ≤ cap (TT v) (nu v) (posAdd s e)
  h2 : ∀ v s e, ((p ^ e * D.ih v s e : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  zero_index_support : ∀ v s s', D.i0 v s s' ≠ 0 → s ∈ TT v ∧ s' ∈ TT v ∧ OtherPar s s'
  pair : ∀ v s s', s ∈ TT v → s' ∈ TT v → OtherPar s s' →
    ((p ^ dLev s s' * (D.i0 v s s' + D.ih v s (dLev s s')) : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  b2 : ∀ v, ((p * D.i2 v : ℕ) : ℤ) ≤ ∑ s, low rb (TT v) (nu v) s
  be_sum : ∀ v s, ((∑ a, ∑ b, D.be v s a b : ℕ) : ℤ) = low rb (TT v) (nu v) s - D.hits v s
  be_le : ∀ v s a b, (D.be v s a b : ℤ) ≤ low rb (TT v) (nu v) s

end PI.UnitaryGroupMassFormula.PadicGainBound
