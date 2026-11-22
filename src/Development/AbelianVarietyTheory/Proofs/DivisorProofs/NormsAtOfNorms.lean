import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.TrivFlag

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def NormsAt (V : Cover Y) (L : LB V.X) (p : ℕ) (W : Y.X.Opens) (f : Y.X → Y.Fn)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∃ r : (L.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.pull V.j).U i, UnitAt x (V.φ (f (V.π x)) * r i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X) (i : (L.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))))

theorem NormsAt.congr {V : Cover Y} {L : LB V.X} {p : ℕ} {W : Y.X.Opens} {f f' : Y.X → Y.Fn}
    {l l' : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : NormsAt V L p W f l) (hf : ∀ x, f x = f' x)
    (hl : ∀ v, resP v = p → ∀ e y, l v e y = l' v e y) : NormsAt V L p W f' l' := by
  obtain rfl : f = f' := funext hf
  obtain ⟨r, h₁, h₂, h₃⟩ := h
  exact ⟨r, h₁, h₂, fun v hv e y hy z yt i a b c => (hl v hv e y).symm.trans (h₃ v hv e y hy z yt i a b c)⟩

end GlobalTheory.TrivFlag

end
