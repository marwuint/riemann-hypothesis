import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB

theorem tsen : Tsen := by
  intro k K _ _ _ _ _
  exact _root_.GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) K (_root_.GlobalTheory.tsenLang_ratFunc k)

end GlobalTheory.NeedB
