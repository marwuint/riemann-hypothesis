import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagGlue

open CategoryTheory Limits TopologicalSpace Opposite
open GlobalTheory.FlagLocal

section Cmp

variable {S T U X : Scheme.{0}}

def pcmp (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback h ≅ Scheme.Modules.pullback k :=
  Scheme.Modules.pullbackComp h g ≪≫ Scheme.Modules.pullbackCongr w

@[reassoc]
theorem pcmp_hom_app (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k) (M : X.Modules) :
    (pcmp h g k w).hom.app M =
      (Scheme.Modules.pullbackComp h g).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M := rfl

end Cmp

theorem ofIso_ι {X : Scheme.{0}} {M M' : X.Modules} {n : ℕ} (fl : Vert.Flag M n) (e : M ≅ M')
    (i : Fin (n + 1)) : (fl.ofIso e).ι i = fl.ι i ≫ e.hom := rfl

variable {B : Scheme.{0}} {ι : Type} {E : ι → B.Modules} {r : ι → ℕ}

variable (E r) in

abbrev Fls {T : Scheme.{0}} (g : T ⟶ B) := ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)

def stepRg {T : Scheme.{0}} {g : T ⟶ B} (fl : Fls E r g) :
    ∀ a (i : Fin (r a + 1)) (V : T.Opens), Set Γ((Scheme.Modules.pullback g).obj (E a), V) :=
  fun a i V => Set.range (((fl a).ι i).app V)

variable (E r) in

abbrev FPt (T : Scheme.{0}) : Type :=
  Σ g : T ⟶ B, {S : ∀ a (i : Fin (r a + 1)) (V : T.Opens), Set Γ((Scheme.Modules.pullback g).obj (E a), V) //
    ∃ fl : Fls E r g, stepRg fl = S}

def fpt {T : Scheme.{0}} (g : T ⟶ B) (fl : Fls E r g) : FPt E r T := ⟨g, stepRg fl, fl, rfl⟩

def FPt.fl {T : Scheme.{0}} (x : FPt E r T) : Fls E r x.1 := x.2.2.choose

def pullFl {S T : Scheme.{0}} (h : S ⟶ T) {g : T ⟶ B} {k : S ⟶ B} (w : h ≫ g = k) (fl : Fls E r g) :
    Fls E r k :=
  fun a => ((fl a).pull h).ofIso ((pcmp h g k w).app (E a))

theorem pullFl_ι {S T : Scheme.{0}} (h : S ⟶ T) {g : T ⟶ B} {k : S ⟶ B} (w : h ≫ g = k) (fl : Fls E r g)
    (a : ι) (i : Fin (r a + 1)) :
    (pullFl h w fl a).ι i = (Scheme.Modules.pullback h).map ((fl a).ι i) ≫ (pcmp h g k w).hom.app (E a) := rfl

def FPt.map {S T : Scheme.{0}} (h : S ⟶ T) (x : FPt E r T) : FPt E r S := fpt (h ≫ x.1) (pullFl h rfl (FPt.fl x))

end GlobalTheory.FlagGlue
