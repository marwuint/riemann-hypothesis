import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory.VolBr

structure IsBallFam {G : Type} [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G) : Prop where

  subset : ∀ r, B r ⊆ Λ

  zero_mem : ∀ r, 0 ≤ r → (0 : G) ∈ B r

  sub_mem : ∀ r r' x y, x ∈ B r → y ∈ B r' → x - y ∈ B (r + r')

  nsmul_iff : ∀ (n : ℕ) (r : ℝ) (x : G), 0 < n → x ∈ Λ → (n • x ∈ B (n * r) ↔ x ∈ B r)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

structure Pair (p : X ⟶ Sp k) where

  L : HermLB p

  A : HermLB p

  r : L.B.ι → X.functionFieldˣ

  r' : A.B.ι → X.functionFieldˣ

  hr : IsRatSec L.B r

  hr' : IsRatSec A.B r'

theorem exists_pair (L A : HermLB p) : ∃ P : Pair p, P.L = L ∧ P.A = A := by
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  exact ⟨⟨L, A, r, r', hr, hr'⟩, rfl, rfl⟩

namespace Pair

variable (P : Pair p)

def loc (a b : ℤ) (f : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) : X.functionField :=
  f * (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b

def H (a b : ℤ) : AddSubgroup X.functionField where
  carrier := {f | ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → RegAt x (P.loc a b f i j)}
  zero_mem' x i j _ _ := ⟨0, by simp [loc]⟩
  add_mem' {f g} hf hg x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    obtain ⟨v, hv⟩ := hg x i j hi hj
    exact ⟨u + v, by rw [map_add, hu, hv]; simp only [loc]; ring⟩
  neg_mem' {f} hf x i j hi hj := by
    obtain ⟨u, hu⟩ := hf x i j hi hj
    exact ⟨-u, by rw [map_neg, hu]; simp only [loc]; ring⟩

def nu (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : ℝ :=
  ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
    Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)

def Bl (a b : ℤ) (R : ℝ) : Set X.functionField :=
  {f | f ∈ P.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ R}

def lc (a b : ℤ) (R : ℝ) : ℝ := Real.log ((P.Bl a b R).ncard : ℝ)

def Rep (a b : ℤ) (M : HermLB p) : Prop :=
  ∃ ρ : M.B.ι → X.functionFieldˣ, IsRatSec M.B ρ ∧
    (∀ (x : X) c i j, x ∈ M.B.U c → x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      UnitAt x ((ρ c : X.functionField) / P.loc a b 1 i j)) ∧
    ∀ (σ : k →+* ℂ) (y : CxPts p σ) c i j, y ∈ ptsIn p σ (M.B.U c) → y ∈ ptsIn p σ (P.L.B.U i) →
      y ∈ ptsIn p σ (P.A.B.U j) →
      Real.log ‖ratVal ((ρ c : X.functionField) / P.loc a b 1 i j) y‖ - (M.φ σ).φ c y / 2 =
        -(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2

structure Good (D : ℕ) (b : ℕ) (s t : X.functionField) : Prop where

  ample : IsAmpleLB P.A.B

  nef : P.A.IsNef D

  pos : 0 < b

  s_mem : s ∈ P.Bl 0 1 1

  s_ne : s ≠ 0

  t_mem : t ∈ P.Bl (-1) b 1

  t_ne : t ≠ 0

  reg : ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ g : X.functionField, RegAt x g →
    RegAt x (g * P.loc (-1) b t i j / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j)

end Pair

namespace IntExample

open GlobalTheory.Points GlobalTheory.CechPic

theorem ratVal_nat {σ : k →+* ℂ} (y : CxPts p σ) (n : ℕ) : ratVal (n : X.functionField) y = n := by
  have h : genericPoint X ∈ (⊤ : X.Opens) := trivial
  have e : (n : X.functionField) = fnOf ⊤ h (n : Γ(X, ⊤)) := (map_natCast _ n).symm
  rw [e, ratVal_fnOf mem_ptsIn_top h, ev_eq mem_ptsIn_top, map_natCast]

theorem isRatSec_one : IsRatSec (LB.triv X) fun _ => 1 := by
  intro i j h
  simp [LB.triv]

def pair : Pair (𝟙 (Sp ℤ)) :=
  ⟨ArithBase.trivShift 0, ArithBase.trivShift (Real.log 3), fun _ => 1, fun _ => 1, isRatSec_one, isRatSec_one⟩

end IntExample

end GlobalTheory.VolBr
