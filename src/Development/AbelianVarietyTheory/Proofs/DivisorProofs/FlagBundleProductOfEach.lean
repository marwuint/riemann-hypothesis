import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

def compIso {X Y B : Scheme.{0}} (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π) (E : B.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback ρ).obj E) ≅ (Scheme.Modules.pullback π).obj E :=
  (Scheme.Modules.pullbackComp p ρ).app E ≪≫ (Scheme.Modules.pullbackCongr w).app E

def Induces {T Y B : Scheme.{0}} (t : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : t ≫ π = g) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback t).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback t).map (fl.ι i) ≫ (compIso t π w E).hom

theorem Induces.congr {T Y B : Scheme.{0}} {t t' : T ⟶ Y} {π : Y ⟶ B} {g : T ⟶ B} {w : t ≫ π = g} {E : B.Modules} {n : ℕ}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n} {fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n}
    (h : Induces t π w fl fl') (e : t = t') (w' : t' ≫ π = g) : Induces t' π w' fl fl' := by
  subst e
  exact h

end GlobalTheory.FlagFamily
