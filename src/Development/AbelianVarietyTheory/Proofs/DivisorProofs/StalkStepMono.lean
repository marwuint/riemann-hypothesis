import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.FlagZ.Univ

variable {X : Scheme.{0}} {N : ℕ}

variable (X N) in

def stalkStd (x : X) : Module.Basis (Fin N) (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  (VB.isFrame_freeFrame X (Fin N)).stalkBasis x trivial

def colSpan {x : X} (g : Matrix (Fin N) (Fin N) (X.presheaf.stalk x)) (l : ℕ) :
    Submodule (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = ∑ i, g i j • stalkStd X N x i}

end GlobalTheory.FlagZ.Univ

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

def stalkStep (τ : ι) (l : ℕ) (y : Fl ι N) :
    Submodule ((Fl ι N).presheaf.stalk y) ((freeModule (Fl ι N) (Fin N)).presheaf.stalk y :) :=
  ⨅ (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y))
    (_ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y), colSpan (g τ).1 l

def sub (τ : ι) (l : ℕ) : VB.Sub (freeModule (Fl ι N) (Fin N)) := VB.Sub.ofStalks (stalkStep ι N τ l)

def freeIso : (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) ≅ freeModule (Fl ι N) (Fin N) :=
  ((VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)).iso (VB.isFrame_freeFrame _ (Fin N))

def F (τ : ι) (i : Fin (N + 1)) : (Fl ι N).Modules := (sub ι N τ i).toMod

def incl (τ : ι) (i : Fin (N + 1)) : F ι N τ i ⟶ (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) :=
  (sub ι N τ i).incl ≫ (freeIso ι N).inv

end GlobalTheory.FlagZ.Univ
