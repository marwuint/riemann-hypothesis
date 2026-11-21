import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace UpperTheory.V.Lit.Desc

def Phi (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if j = i.rev then (-1) ^ (i : ℕ) else 0

def snd {K : Type} [Field K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Phi K n * (g⁻¹)ᵀ * (Phi K n)⁻¹

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end UpperTheory.V.Lit.Desc

namespace UpperTheory.V.Lit

end UpperTheory.V.Lit
