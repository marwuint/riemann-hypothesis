import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.ConstLat

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

namespace RelEx

end RelEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def eigAt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) (k : ℕ) : Sym E →₀ ℤ :=
  match (letters Dw)[k]? with
  | some z => Finsupp.single (a, R, .inl (z.1, (z.2 : ℕ))) s
  | none => 0

def eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => eigAt Dw a R 1 k
  | .inr k => eigAt Dw a R (-1) (Fin.rev k)

@[simp] theorem eigSym_inl (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inl k) = eigAt Dw a R 1 k := rfl

@[simp] theorem eigSym_inr (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inr k) = eigAt Dw a R (-1) (Fin.rev k) := rfl

end GlobalTheory.ConstLat

end
