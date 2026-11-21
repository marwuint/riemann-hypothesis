import Formalism.LocalToGlobal.Columns.RecChainCUnfPol
import Formalism.LocalToGlobal.Columns.RefXi1Above

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Vec

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}

def VecAt (E : Type) [Field E] [NumberField E] (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (all : Prop) : Type :=
  {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal // all ∨ v = 0}

instance (all : Prop) : Finite (VecAt E n SG all) := Subtype.finite

instance vecAct (Λ : LevFam E K n SG) (all : Prop) : MulAction ↥Λ.grp (VecAt E n SG all) where
  smul h v := ⟨fun w => ((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w), by
    rcases v.2 with h1 | h1
    · exact Or.inl h1
    · right
      funext w
      rw [h1]
      exact Matrix.mulVec_zero _⟩
  one_smul v := Subtype.ext (funext fun w => Matrix.one_mulVec _)
  mul_smul g h v := Subtype.ext (funext fun w => by
    show ((((g * h : ↥Λ.grp) : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w) =
      ((g.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec
        (((h.1 w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).mulVec (v.1 w))
    rw [Matrix.mulVec_mulVec]
    rfl)

end Vec

end Formalism.L2.Col
