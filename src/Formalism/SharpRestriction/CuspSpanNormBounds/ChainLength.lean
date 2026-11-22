import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
