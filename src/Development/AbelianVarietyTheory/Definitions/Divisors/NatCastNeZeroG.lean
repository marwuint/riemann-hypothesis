import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

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

theorem eigAt_of_lt (a : ℕ → Bool) (R : Option ℝ) (s : ℤ) {k : ℕ} (h : k < (letters Dw).length) :
    eigAt Dw a R s k = Finsupp.single (a, R, .inl ((letters Dw)[k].1, ((letters Dw)[k].2 : ℕ))) s := by
  unfold eigAt
  rw [List.getElem?_eq_getElem h]

@[simp] theorem eigSym_inl (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inl k) = eigAt Dw a R 1 k := rfl

@[simp] theorem eigSym_inr (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (k : Fin g) :
    eigSym Dw a R (.inr k) = eigAt Dw a R (-1) (Fin.rev k) := rfl

theorem expo_eigSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} (i : Fin g ⊕ Fin g) :
    expo Dw (eigSym Dw a R i) = expo Dw (wholeSym a R i) := by
  have key : ∀ (s : ℤ) (k : ℕ), expo Dw (eigAt Dw a R s k) = expo Dw (Finsupp.single (a, R, .inr k) s) := by
    intro s k
    funext x
    unfold eigAt expo
    cases h : (letters Dw)[k]? with
    | none => simp [letterOf, h]
    | some z =>
      dsimp only
      rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      have e : letterOf Dw (.inl (z.1, (z.2 : ℕ))) = letterOf Dw (.inr k) := (dif_pos z.2.2).trans h.symm
      dsimp only
      rw [e]
  cases i <;> exact key _ _

end GlobalTheory.ConstLat

end
