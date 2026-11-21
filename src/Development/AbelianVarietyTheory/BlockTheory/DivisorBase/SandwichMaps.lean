import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich

namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

section Eigen

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Λ : Type} [CommRing Λ] {h : ℕ}

def eig (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) : Submodule C (Fin h → C) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
    (algebraMap O C (σ a))

end Eigen

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h h' : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def actT (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρT a).map (padicToO p O)

def redC {m n : ℕ} (X : Matrix (Fin m) (Fin n) (Ainf p O)) : (Fin n → C) →ₗ[C] (Fin m → C) :=
  Matrix.toLin' (X.map ((algebraMap O C).comp (fontaineTheta O p)))

def alC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.F

def bC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.G

end Datum

end GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
