import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

section OneField

variable {K : Type} [Field K] [NumberField K]

section Geo

variable (G : Geo K) (s : Fin G.D → Fin G.N → K) (σ : K →+* ℂ)

def mulPow {a j l : ℕ} (h : j + a = l) (α : MonoDeg (Fin G.D) a) : G.Sec j →ₗ[K] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) α ((Nat.cast_add j a).symm.trans (congrArg _ h))

variable {G s} (hs : G.IsGood s)

def symOnGr {a j l : ℕ} (h : j + a = l) (V : Submodule K (G.Sec l)) :
    gr (G.ideal s) a V →ₗ[K] SymTarget G.str G.L₂ G.isLB (G.sec s) a j :=
  Submodule.liftQ _ (hs.sym h V) (ker_sym _ _ _ _ _ _ _ _ _ _ V).ge

end Geo

section Data

variable (X : Data K) (s : Fin X.D → Fin X.N → K) (σ : K →+* ℂ)

theorem add_sub_D : X.D + (X.T - X.D) = X.T := Nat.add_sub_cancel' ((Nat.le_succ _).trans X.le_T)

theorem sub_add {a : ℕ} (ha : a ≤ X.a₀) : X.T - a + a = X.T :=
  Nat.sub_add_cancel (by have := X.a₀_add; omega)

def spaceP : Submodule K (X.Sec X.T) :=
  ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)

def spaceV : Submodule K (X.Sec X.T) := X.global X.T ⊔ spaceP X s

instance finiteDimensional_spaceP : FiniteDimensional K (spaceP X s) := by
  unfold spaceP
  infer_instance

instance finiteDimensional_spaceV : FiniteDimensional K (spaceV X s) := by
  unfold spaceV
  infer_instance

variable {X s} (hs : X.IsGood s)

end Data

end OneField

variable {F : Type} [Field F] [NumberField F] (X : Data F)

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

variable {E}

structure Ranks {s : Fin X.D → Fin X.N → E} (hs : (X.baseChange E).IsGood s) : Prop where

  bijective : ∀ (a : ℕ) (ha : a ≤ (X.baseChange E).a₀),
    Function.Bijective (symOnGr hs (sub_add (X.baseChange E) ha) (spaceV (X.baseChange E) s))

  finrank_eq : (Module.finrank E (spaceV (X.baseChange E) s) : ℤ) =
    X.R * X.del + Module.finrank E (spaceP (X.baseChange E) s)

  le_d : X.R * X.del ≤ (X.d : ℤ)

  d_pos : 0 < X.d

  z_nonneg : 0 ≤ X.z

  z_le_one : X.z ≤ 1

  one_sub_mul : (1 - X.z) * X.d = X.R * X.del

def Complexify : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (β : (F →+* ℂ) → ℝ), IsTotallyComplex F → (∀ σ, 0 < β σ) →
    X.MulStable → X.MulBound β →
      (∀ σ, X.MulBoundAt σ (β σ)) ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], (X.baseChange E).MulStable

end GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
