import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.ArithmeticGeometry.IwasawaModules.SpanFinrankMaximalIdealLeTwo

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w u₁ u₂

section Coordinates

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def segreVec (pt : MRingOver o ι →ₐ[o] Ω) : ((k : K) → ι k) → Ω :=
  fun i => ∏ k, pt (X ⟨k, i k⟩)

end Coordinates

section ProjBundle

variable {K : Type*} [Fintype K]

def extIdx (ι : K → Type w) (τ : Type w) : Option K → Type w
  | none => τ
  | some k => ι k

instance extIdx.fintype {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ] :
    (k : Option K) → Fintype (extIdx ι τ k)
  | none => inferInstanceAs (Fintype τ)
  | some k => inferInstanceAs (Fintype (ι k))

variable {ι : K → Type w} [∀ k, Fintype (ι k)] {τ : Type w} [Fintype τ]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section PolyNum

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def monoList {N : ℕ} (mono : Fin N →₀ ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun l => List.replicate (mono l) l

variable {F : Type*} [Field F]

end PolyNum

section Pairs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

structure VPair (K : Type*) [Fintype K] (O : Type*) [CommRing O] (ι : K → Type*) [∀ k, Fintype (ι k)] where

  y : K → ℤ

  b : K → ℤ

  f : MRingOver O ι

  g : MRingOver O ι

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {Ω : Type*} [Field Ω] [Algebra O Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end Pairs

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def trivLat {ι' : Type*} (x : ι' → Ω) (N : ℕ) (i : ι') : AddSubgroup (Fin N → Ω) where
  carrier := {e | ∀ q, e q ∈ chartRing o x i}
  add_mem' ha hb q := add_mem (ha q) (hb q)
  zero_mem' _ := zero_mem _
  neg_mem' ha q := neg_mem (ha q)

variable {o}

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
