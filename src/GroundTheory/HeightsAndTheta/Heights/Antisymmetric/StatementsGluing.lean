import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

section Join

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type*}
  {E : Type*} [AddCommGroup E] [Module Ω E] {r : ℕ}

def joinPt (x : ι → Ω) (z : κ → Ω') : ι × κ → Ω' :=
  segreJoin (fun i => algebraMap Ω Ω' (x i)) z

def pullbackLat {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ) :
    AddSubgroup (Ω' ⊗[Ω] E) :=
  AddSubgroup.closure {w | ∃ a ∈ chartRing ℤ (joinPt x z) q, ∃ v ∈ B.lat q.1,
    w = a • ((1 : Ω') ⊗ₜ[Ω] v)}

end Join

section AddBlock

universe u

def addBlockIdx {K : Type*} (ι : K → Type u) (κ : Type u) : Option K → Type u
  | none => κ
  | some k => ι k

instance addBlockIdx.fintype {K : Type*} (ι : K → Type u) [∀ k, Fintype (ι k)] (κ : Type u)
    [Fintype κ] : ∀ o, Fintype (addBlockIdx ι κ o)
  | none => ‹Fintype κ›
  | some k => (inferInstance : Fintype (ι k))

end AddBlock

end GroundTheory.Heights₂.Heights
