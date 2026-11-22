import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartOfIsFinitePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullPointIdentityDegeneration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUniformizationIdentityPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionFiniteFlatIff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit IsLocalRing
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R]

theorem tors_of_isPull [IsNoetherianRing R] {D : DegPre R} {k : ℕ} {T T' : Over (Sp R)} (h : T' ⟶ T) {g : GtPt D T}
    {g' : GtPt D T'} (hp : GtPt.IsPull h.left g g') (hg : FlatIsoUnitGenerator.GtTors k g) : FlatIsoUnitGenerator.GtTors k g' := by
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents D
  obtain ⟨x, rfl⟩ := (Φ T).surjective g
  obtain ⟨x', rfl⟩ := (Φ T').surjective g'
  rw [isPull_iff_comp hΦ] at hp
  rw [tors_iff hΦ] at hg ⊢
  rw [← hp, ← MonObj.comp_pow, hg, MonObj.comp_one]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.TorsionFormCompare
