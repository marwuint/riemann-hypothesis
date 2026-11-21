import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Finset

section Numbers

variable {n' : ℕ}

structure IsPart (r0 : ℕ) (nu : Fin n' → ℕ → ℤ) : Prop where
  nonneg : ∀ s i, 0 ≤ nu s i
  anti : ∀ s i, 1 ≤ i → nu s (i + 1) ≤ nu s i
  what₂ : ∀ s i, r0 < i → nu s i = 0

def al (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 1 - nu s 2 else 0

def cap (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 2 else nu s 1

def sz (rb : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := ∑ i ∈ Icc 1 rb, nu s i

def low (rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := sz rb nu s - al TT nu s

def OtherPar (s s' : Fin n') : Prop := s'.val % 2 ≠ s.val % 2

instance (s s' : Fin n') : Decidable (OtherPar s s') := inferInstanceAs (Decidable (_ ≠ _))

def dLev (s s' : Fin n') : ℕ := (s'.val + n' - s.val) % n'

end Numbers

section Series

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

structure ValR : Prop where
  val : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc
  p_nonunit : ((p : Kc))⁻¹ ∉ Oc

end Series

structure Shape where
  nV : ℕ
  n' : Fin nV → ℕ
  r0 : ℕ
  r1 : ℕ

namespace Shape

variable (Sh : Shape)

abbrev ZV : Type := Σ v : Fin Sh.nV, FormalGroupSystem.Zidx (Sh.n' v) Sh.r0 Sh.r1

abbrev FrV : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × Fin Sh.r0

abbrev Wt : Type := ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℤ

variable {Kc : Type} [Field Kc] (Oc : Subring Kc)

variable (p : ℕ)

end Shape

section Core

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (Sh : Shape)

structure HidaSetting (rb : ℕ) (nu : Sh.Wt) (vp : Kc) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  valR : ValR p Oc
  vp_pow : vp ^ (p ^ 2 - 1) = (p : Kc)
  even : ∀ v, Even (Sh.n' v)
  two_le : ∀ v, 2 ≤ Sh.n' v
  part : ∀ v, IsPart Sh.r0 (nu v)
  rb_ge : Sh.r0 ≤ rb

end Core

end Formalism.MainNotions.KernelEntryData
