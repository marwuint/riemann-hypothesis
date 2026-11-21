import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst

noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.GenusZero

open GlobalTheory.ToricData GlobalTheory.UnifZero

instance isIso_pullback_hom {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [IsIso G.hom] :
    IsIso ((Over.pullback f).obj G).hom := (inferInstance : IsIso (pullback.snd G.hom f))

instance isIso_unit_hom (S : Scheme.{0}) : IsIso (𝟙_ (Over S)).hom := (inferInstance : IsIso (𝟙 S))

variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [IsIso G.hom]

instance (e : ℕ) : IsIso (thickObj R I e G).hom := isIso_pullback_hom _ _

instance (e : ℕ) : IsIso (thickObj R I e (zeroData R I).toPre.P.A).hom := isIso_pullback_hom _ (𝟙_ _)

instance : IsIso (zeroData R I).toPre.P.A.hom := isIso_unit_hom _

variable {R I G}

end GlobalTheory.ZH.GenusZero
end
