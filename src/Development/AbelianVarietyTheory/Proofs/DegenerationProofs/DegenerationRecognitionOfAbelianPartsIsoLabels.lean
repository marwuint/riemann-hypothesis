import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.Recognition

theorem urec_of_abelian : UrCSt → URecSt := by
  intro hC R _ _ D D' h1 h2 h3 h4 C _ _ _ _ _ N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt
  obtain ⟨hA, hg⟩ := _root_.GlobalTheory.MatchParts.match_parts C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt
  obtain ⟨e, hB, hT⟩ := _root_.GlobalTheory.MatchTerm.main C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA
  obtain ⟨I, hOB, hl, hG⟩ := hC R D D' h1 h2 h3 h4 C N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt hA hg e hB hT
  obtain ⟨J, hJ, hJe, hOG⟩ := _root_.GlobalTheory.Ex.RecPeriods.exists_iso_onG C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA e hB hT I hOB
  subst hJ hJe
  exact ⟨J, _root_.GlobalTheory.LabelsAgree.main C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA J hB hOG hl, hG⟩
end GlobalTheory.Ex.Recognition
