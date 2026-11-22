import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

section Sets

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

def StdAtT {n : ℕ} (d : Deco E n ST SG) : Prop := ∀ P : ST, d.at P.1 = stdAt E n P.1

end Sets

section Table

variable {X : Fields} {a b : ℕ}

def RatAt (A : Amb X) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ x ∈ divLat cA (homAt Sall N N'), Ξ x ≠ 0 →
    ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' cB x) m

end Table

end GlobalTheory.IndefiniteRowSideFullHecke.StandardKernelAtTorus
