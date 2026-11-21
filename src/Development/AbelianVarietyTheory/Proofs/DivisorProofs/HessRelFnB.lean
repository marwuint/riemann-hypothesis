import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

namespace Cover

variable (V : Cover Y)

def FinInd (A : Adl C Y) (B : LB V.X) (r : (B.pull V.j).ι → V.G.functionFieldˣ) : Prop :=
  IsRatSec (B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) * r i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit) →
      A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * (r i : V.G.functionField))))

end Cover

end GlobalTheory.Mean4O
