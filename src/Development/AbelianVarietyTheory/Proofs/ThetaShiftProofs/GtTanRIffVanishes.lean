import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNeZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

noncomputable section

namespace GlobalTheory.ConstModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)
open scoped CategoryTheory.Obj

section Through

variable {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R'']
  {f : R →+* R'} {f' : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''}

structure IsComp (p : IsPullDeg f D D') (q : IsPullDeg f' D' D'') (r : IsPullDeg (f'.comp f) D D'') : Prop where
  proj_eq : proj r = proj q ≫ proj p
  xe_eq : ∀ x, r.xe x = p.xe (q.xe x)
  tri : ∀ (Y : Scheme.{0}) (x : Y ⟶ D''.P.A.left) (y : Y) j i k, proj p (proj q (x y)) ∈ D.P.L.U j →
    proj q (x y) ∈ D'.P.L.U i → x y ∈ D''.P.L.U k →
    Geo.Tor.gw r.w x y j k = Geo.Tor.gw p.w (x ≫ proj q) y j i * Geo.Tor.gw q.w x y i k

namespace IsComp

end IsComp

end Through

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)]

end GlobalTheory.ConstModel
