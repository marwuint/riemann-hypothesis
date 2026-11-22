import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SimilitudesCorrespond
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm (IsOver PullsBack lowerCoeff levelMapF endF relGroup trivAt)

namespace GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l l₂ : Level H}

def CxPt (Xo : Moduli Dw l) (c : Coeff l) : Type :=
  {y : Sp ℂ ⟶ Xo.XF c // y ≫ pullback.snd _ _ = spMap c.F.val.toRingHom}

def LiesOver (h : l.Dvd l₂) {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}
    (y₂ : CxPt Xo₂ c₂) (y : CxPt Xo c) : Prop :=
  ∃ π : Xo₂.X ⟶ Xo.X, IsOver h Xo Xo₂ π ∧ PullsBack Xo Xo₂ π ∧
    y₂.1 ≫ pullback.fst _ _ ≫ π = y.1 ≫ pullback.fst _ _

open Classical in

def levDeg (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) : ℕ :=
  if k : ∃ n, 0 < n ∧ ∀ y : CxPt Xo c, Nat.card {y₂ : CxPt Xo₂ c₂ // LiesOver h y₂ y} = n then Nat.find k else 1

theorem levDeg_pos (h : l.Dvd l₂) (Xo : Moduli Dw l) (c : Coeff l) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂) :
    0 < levDeg h Xo c Xo₂ c₂ := by
  classical
  unfold levDeg
  split_ifs with k
  · exact (Nat.find_spec k).1
  · exact one_pos

end GlobalTheory.ShFam.Pad
