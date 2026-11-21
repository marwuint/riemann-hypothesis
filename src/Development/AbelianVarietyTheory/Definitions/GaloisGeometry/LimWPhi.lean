import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasLevelOffOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GenOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong MvPolynomial

namespace GlobalTheory.CongL

def DGen (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  (∏ i : Fin a, ∏ j : Fin a, if i = j then 1 else ∏ c ∈ Finset.range a, (X i ^ (c + 1) - X j ^ (c + 1))) *
  (∏ i : Fin a, ∏ j : Fin a, ∏ k : Fin a, if j = i ∨ j = k then 1 else (X i * X k - X j ^ 2)) *
  (∏ m ∈ (Finset.univ : Finset (Fin a → Fin (a + 1))).filter (fun m => (∑ i, (m i : ℕ)) = a ∧ m ≠ fun _ => 1),
    ((∏ i, X i ^ (m i : ℕ)) - ∏ i, X i))

def GapJ (a : ℕ) (J : Multiset ℤ) : Prop :=
  ∀ i : ℕ, i + 1 < a →
    (J.sort (· ≤ ·)).getD (i + 1) 0 - (J.sort (· ≤ ·)).getD 0 0 > (a : ℤ) * ((J.sort (· ≤ ·)).getD i 0 - (J.sort (· ≤ ·)).getD 0 0)

def WtLac : SeedWtU := fun E _ _ _ l _ a ι w₀ v' U U' =>
  SameWtOff ι w₀ v' U U' ∧ ∃ τ₀ : E →+* ℂ, OverPl ι τ₀ v' ∧ ∀ lam, HasWeightAt U' τ₀ lam → ∀ J : Multiset ℤ,
    J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

end GlobalTheory.CongL

end
