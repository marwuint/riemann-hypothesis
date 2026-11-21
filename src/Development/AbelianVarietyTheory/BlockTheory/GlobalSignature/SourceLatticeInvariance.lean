import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance

open Formalism.L2.Col

section Defs

variable {E : Type} [Field E] [NumberField E]

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) :=
  ⟨0, 1, one_notMem P, by simp⟩

theorem intAt_add {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  refine ⟨s' * r + s * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
  ring

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩

def DegOneUnram (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  (qOf P).Prime ∧ ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2

def depthSub (P : HeightOneSpectrum (𝓞 E)) (D : ℕ) : AddSubgroup E where
  carrier := {a | IntAt P ((qOf P : E) ^ D * a)}
  add_mem' := fun {a b} ha hb => by
    show IntAt P _
    rw [mul_add]
    exact intAt_add ha hb
  zero_mem' := by
    show IntAt P _
    rw [mul_zero]
    exact intAt_zero P
  neg_mem' := fun {a} ha => by
    show IntAt P _
    rw [mul_neg]
    exact intAt_neg ha

def unfoldAB {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (A B : ℕ) {n' c' n c : ℕ}
    (Psi : Loc.SF E K (n' + c') (n + c)) : Loc.SF E K n' n :=
  Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Psi

end Defs

end GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance
