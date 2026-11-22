import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionForStatement

namespace GlobalTheory.Published

theorem arCalc_of_form_mix_projection : ArFormExists → ArMix → HeightProjection → ArCalc := fun hF hM hP =>
  have hE : ArExists := _root_.GlobalTheory.Published.arExists_of_form_of_mix hF hM
  have hC : ArChange := arChange_of_arMix hE hM
  ⟨hE, hC, _root_.GlobalTheory.Published.arShift_of_arChange hE hC, hM, GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula hP, arIso_holds, _root_.GlobalTheory.Published.arMetric_of_arMix hE hM⟩

end GlobalTheory.Published
