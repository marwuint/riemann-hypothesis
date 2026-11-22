import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsTwoTorsionWeilDegenerate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenWeilModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ext {ξ : Spec (CommRingCat.of Ω) ⟶ X} {k : Type} [Field k] (i : Ω →+* k) :
    Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl

theorem unique {G : Over X} [GrpObj G] {L : LB G.left} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    {e e' : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (h : GenWeil G L ξ n e) (h' : GenWeil G L ξ n e')
    {x g : Over.mk ξ ⟶ G} (hx : x ^ n = 1) (hg : g ^ n = 1) : e x g = e' x g := by
  let i := algebraMap Ω (AlgebraicClosure Ω)
  let c : (AlgebraicClosure Ω)ˣ := Units.map i.toMonoidHom (e x g)
  have h1 := (h.weil x g hx hg _ i (ext i ≫ x) (ext i ≫ g) c rfl rfl).2 rfl
  have h2 := (h'.weil x g hx hg _ i (ext i ≫ x) (ext i ≫ g) c rfl rfl).1 h1
  exact Units.ext (i.injective h2)

theorem unitOn_ext {k : Type} [Field k] (i : Ω →+* k) (u : Ωˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map i.toMonoidHom u) := by
  ext
  exact congrArg (fun f => f.hom (u : Ω)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)).symm

theorem unitOn_bij {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

end GlobalTheory.CompanionTheory.Ar.GenWeilModel
