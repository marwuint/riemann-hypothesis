import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps

section Defs

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

structure IsProjSurface : Prop where

  isIntegral : IsIntegral T

  dim_eq : topologicalKrullDim T = 2

  isProjOver : IsProjOver (strHom k T)

variable [IsIntegral T]

end Defs

inductive HasFlag {T : Scheme.{0}} : T.Modules → List (LB T) → Prop

  | nil {E : T.Modules} (h : IsZero E) : HasFlag E []

  | cons {L : LB T} {l : List (LB T)} (S : ShortComplex T.Modules) (hS : S.ShortExact)
      (hL : L.IsLB) (e : S.X₃ ≅ toMod L) (h : HasFlag S.X₁ l) : HasFlag S.X₂ (L :: l)

structure IsGenFinite {T' T : Scheme.{0}} [IsIntegral T'] (ρ : T' ⟶ T) (d : ℕ) : Prop where

  isDominant : IsDominant ρ

  pos : 0 < d

  finrank_eq : letI := (ρ.stalkMap (genericPoint T')).hom.toAlgebra
    Module.finrank (T.presheaf.stalk (ρ (genericPoint T')))
      (T'.presheaf.stalk (genericPoint T')) = d

end GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
