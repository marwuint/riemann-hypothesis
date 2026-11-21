import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := _root_.GlobalTheory.MixHt.exists_isMix_of_arch hI hR
  refine ⟨_root_.GlobalTheory.MixHt.arFormExists_of_isMix hI hE, _root_.GlobalTheory.MixHt.arMix_of_mixHt hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', _root_.GlobalTheory.MixHt.heightProj k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
