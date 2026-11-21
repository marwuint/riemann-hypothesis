import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def SplitK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (io : K →+* Ω) (w : Over.mk (spMap io ≫ ξ) ⟶ t.G), w ^ q = 1 →
    ∃ w₀ : Sp K ⟶ t.G.left, spMap io ≫ w₀ = w.left

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker

variable {t} in

def Agree {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ} (c c' : TorsChar t x q) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G),
    w ^ q = 1 → c.χ B w = c'.χ B w

variable {t} in

def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

end Chars

end GlobalTheory.HtGen
