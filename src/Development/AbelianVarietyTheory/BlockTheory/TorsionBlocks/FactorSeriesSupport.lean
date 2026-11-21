import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

open Formalism.BasicNotions

def IsLabel (N : ℕ) {g : ℕ} (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0

def rootExp (N g : ℕ) : ℕ := (Finset.Icc 1 N).lcm fun d => g ^ d - 1

def IsPowLabel {g : ℕ} [Fact g.Prime] (a : ℤ) (f f' : (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map fun x => x ^ a

variable (D : D7)

theorem IsPowLabel.unique {g : ℕ} [Fact g.Prime] {a : ℤ} {f f₁ f₂ : (ZMod g)[X]}
    (h₁ : IsPowLabel a f f₁) (h₂ : IsPowLabel a f f₂) (m₁ : f₁.Monic) (m₂ : f₂.Monic) : f₁ = f₂ := by
  have h : Formalism.CyclotomicNorms.rootsBar f₁ = Formalism.CyclotomicNorms.rootsBar f₂ := h₁.trans h₂.symm
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  have e : ∀ p : (ZMod g)[X], p.Monic → p.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) =
      ((Formalism.CyclotomicNorms.rootsBar p).map fun x => X - C x).prod := fun p hp =>
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      (IsAlgClosed.card_roots_eq_natDegree)).symm
  rw [e f₁ m₁, e f₂ m₂, h]

theorem rootExp_ne_zero (N g : ℕ) (hg : 2 ≤ g) : rootExp N g ≠ 0 := by
  unfold rootExp
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨d, hd, h⟩
  have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.1 hd).1; omega
  have : 1 < g ^ d := Nat.one_lt_pow hd1 (by omega)
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

end
