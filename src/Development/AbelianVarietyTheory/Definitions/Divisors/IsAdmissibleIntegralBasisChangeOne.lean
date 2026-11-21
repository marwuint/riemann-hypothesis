import Mathlib
import GroundTheory.FunctionField.PlaceBridge

set_option autoImplicit false

noncomputable section

open scoped IntermediateField Polynomial

namespace GlobalTheory.Nef

def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F

def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring

def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)

def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)

def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)

def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1

def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite

def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det

def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)

def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1

def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)

def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E

def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)

def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det

def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)

namespace Lib

end Lib

end GlobalTheory.Nef
