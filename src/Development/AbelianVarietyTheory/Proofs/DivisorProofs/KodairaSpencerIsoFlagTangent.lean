import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFirstOrderDeformation

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (h1 : X ≫ Xo.s = sOf c _) (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x)
    (M : ι → K) : GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1]
    unfold sOf
    have e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) =
        algebraMap c.F (DualNumber K) := (GlobalTheory.FlagTan.dir c M).comp_algebraMap
    rw [spMap_comp_spMap, ← RingHom.comp_assoc, e]
  · rw [← Category.assoc, spMap_comp_spMap, ← h2]
    congr 2
    ext z <;> simp

end GlobalTheory.FlagTan
