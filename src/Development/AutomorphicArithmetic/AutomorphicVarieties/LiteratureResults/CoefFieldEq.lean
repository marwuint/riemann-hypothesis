import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.V.Published.Kato Polynomial
open CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Lit

def pet (M k : ℕ) (f h : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Gamma1 M, ∫ z in ModularGroup.fd, petersson (k : ℤ) f h (γ.out⁻¹ • z)

def dil (d : ℕ) (hd : 0 < d) (g : ℍ → ℂ) : ℍ → ℂ := fun z => g ((⟨(d : ℝ), Nat.cast_pos.2 hd⟩ : {x : ℝ // 0 < x}) • z)

structure Primitive (k M : ℕ) (χ : DirichletCharacter ℂ M) (f : CuspForm (Gamma1 M) (k : ℤ)) : Prop where
  char : HasChar k χ f
  new : ∀ (M' d : ℕ) (h : M' ∣ M) (hd : 0 < d), M' ≠ M → d * M' ∣ M → ∀ χ' : DirichletCharacter ℂ M',
    DirichletCharacter.changeLevel h χ' = χ → ∀ g : CuspForm (Gamma1 M') (k : ℤ), HasChar k χ' g → pet M k f (dil d hd g) = 0
  eig : ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∃ lam : ℂ, IsEigAt k χ f p lam
  one : coef f 1 = 1

variable {l : ℕ} [Fact l.Prime]

end UpperTheory.V.Lit
