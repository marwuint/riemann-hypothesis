import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

namespace Formalism.L2.Col

open Module Module.End Polynomial

section Genus

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def UnimodGenusLoc (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  IsCMUnram E → ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
    SameGenus (hStd E n) (stdLat E n) N

def UnimodGenusLocAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), UnimodGenusLoc E n

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def UnimodGenus : Prop :=
  ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Formalism.HermitianLatticesTheory.IsUnimodular (hStd E n) N →
    ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

end Genus

section Counting

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

def wSeq {n : ℕ} (lam : DomWeight n) : ℕ → ℝ := fun i => if h : i < n then ((lam.w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylDim {n : ℕ} (lam : DomWeight n) : Prop :=
  (Nat.card (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ℝ) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (wSeq lam) n

end Counting

abbrev MinkowskiBound : Prop := Formalism.HermitianLatticeCounting.S6.MinkowskiBound

end Formalism.L2.Col
