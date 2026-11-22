import Mathlib
import Formalism.FormalGroupWitt.Statement

noncomputable section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

def PowerCongruenceIffEqual : Prop :=
  ∀ (l d s s' : ℕ), 2 ≤ l → s < d → s' < d →
    ((l ^ d - 1 : ℕ) : ℤ) ∣ (l : ℤ) ^ s - (l : ℤ) ^ s' → s = s'

def cob {M Q : Type} [AddCommGroup M] [AddCommGroup Q] (φ : M → Q) (a b : M) : Q :=
  φ (a + b) - φ a - φ b

def NormAllAlpha : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm tr : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) → (∀ α, algebraMap Z O (tr α) = star α + α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ x : Q, x + x = 0 → x = 0) →
    ∀ (α α' : O) (u : M), φ ((2 : O) • u) = (4 : Z) • φ u →
      φ (α • u) = nm α • φ u → φ (α' • u) = nm α' • φ u →
      φ ((α + α') • u) = nm (α + α') • φ u

def UnitaryInvariance : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
      ∀ u : n → M, ∑ i, φ (∑ j, δ i j • u j) = ∑ j, φ (u j)

def HyperbolicSplit : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
      (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
      ∀ t t' : ι → M,
        ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e)) = ∑ e, cob φ (t e) (t' e)

def IntegerMeanLog : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    0 ≤ ∑ φ : K →+* ℂ, Real.log ‖φ (x : K)‖

def WeberRoot : Prop :=
  ∀ (x j : ℂ) (s : ℤ), (s = 16 ∨ s = -16) → IsIntegral ℤ j → (x - (s : ℂ)) ^ 3 = j * x →
    IsIntegral ℤ x ∧ x ≠ 0

end Formalism.HermitianLattices.IntegralLatticeDensity
