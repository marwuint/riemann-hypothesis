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

def trivBundle {ι' : Type*} (x : ι' → Ω) (N : ℕ) : ChartBundle o x N (Fin N → Ω) where
  lat := trivLat o x N
  stable i a ha e he q := by
    show a * e q ∈ chartRing o x i
    exact mul_mem ha (he q)
  frame i _ := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨Pi.basisFun Ω (Fin N), (Pi.basisFun Ω (Fin N)).linearIndependent,
      (Pi.basisFun Ω (Fin N)).span_eq, fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    constructor
    · intro he
      exact ⟨e, he, by simpa using ((Pi.basisFun Ω (Fin N)).sum_repr e).symm⟩
    · rintro ⟨a, ha, rfl⟩ q
      have : (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q = a q := by
        simp [Finset.sum_apply, Pi.single_apply]
      show (∑ q', a q' • (Pi.basisFun Ω (Fin N)) q') q ∈ chartRing o x i
      rw [this]
      exact ha q
  overlap i j hi _ e he := by
    choose m hm using fun q => exists_pow_mul_mem_chartRing x i j hi (he q)
    refine ⟨∑ q, m q, fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : ((x i / x j) ^ (∑ q, m q) • e) q =
        (x i / x j) ^ (∑ q, m q - m q) * ((x i / x j) ^ m q * e q) := by
      rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    exact mul_mem (pow_mem (div_mem_chartRing x j i) _) (hm q)

variable {o}

theorem mem_trivBundle {ι' : Type*} {x : ι' → Ω} {N : ℕ} {i : ι'} {e : Fin N → Ω} :
    e ∈ (trivBundle o x N).lat i ↔ ∀ q, e q ∈ chartRing o x i :=
  Iff.rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
