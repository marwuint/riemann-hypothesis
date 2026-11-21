import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Norms (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (f (V.π x)) * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      a σ y = Real.log ‖ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z‖ - (L.φ _).φ (i PUnit.unit) y' / 2) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))))

theorem Norms.congr {V : Cover Y} {L : HermLB V.p} {f f' : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l l' : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (hf : ∀ x, f x = f' x)
    (ha : ∀ σ y, a σ y = a' σ y) (hl : ∀ v e y, l v e y = l' v e y) : Norms V L f' a' l' := by
  obtain rfl : f = f' := funext hf
  obtain rfl : a = a' := funext₂ ha
  obtain rfl : l = l' := funext₃ hl
  exact h

end GlobalTheory.CoverNorm
