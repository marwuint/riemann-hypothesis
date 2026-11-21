import Mathlib
import GroundTheory.AutomorphicForms.SphericalIntegral

open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

abbrev Pos : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Res (t : ℕ) : Type := 𝒪[F] ⧸ Ideal.span {uniformizer F ^ t}

abbrev HData (l : Fin n → ℕ) : Type := ∀ p : Pos n, Res F (l p.1.1)

variable {F n}

variable (F n) in

abbrev HDataDeg (k : ℕ) : Type := Σ l : {l : Fin n → ℕ // ∑ i, l i = k}, HData F n l.1

end GlobalTheory.HermCount
