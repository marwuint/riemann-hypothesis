import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section Model

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt

variable {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Man.pull (M : Man e) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (u : M.Fun) :
    ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun σ z => u (ε σ) (π σ z)

variable (K : Calc M) (ε : (k →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts p σ → M.X (ε σ)) (ν : ℝ)
  {ι : Type} [Fintype ι] (L : ι → HermLB p) (v : ι → K.V)

def Calc.ChernOn : Prop := ∀ u, M.Smooth u → ∀ hu hc (n : Option ι → ℤ) (f : M.Fun), M.Smooth f →
  chInt (ArInt.comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) n) e (M.pull ε π f) =
    ν * M.int (fun _ => K.c1 (∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u)) f

def Calc.NumOn [IsIntegral X] : Prop := ∀ u, M.Smooth u → ∀ hu hc (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
  IsArFun (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu hc) L) e Φ → ∀ a : Option ι → ℝ,
    Φ (lin a ^ (e + 1)) = ν * K.top (∑ i, a (some i) • v i + a none • K.ar u)

end Model

variable {D : D7} {Y : ShimX D.what₂.Tau} {T : Real0 Y} (P : T.Pts)

end GlobalTheory.Mean4O
