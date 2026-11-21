import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := _root_.GlobalTheory.LTPeriod.main l P AI hT K _ hn
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.ltChar_hom l P K x hxu (_root_.GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := _root_.GlobalTheory.ContCharUnitsOL.main l K LL τ₀ c hcont
  exact ⟨χ, hχc, _root_.GlobalTheory.HWL.charRep_crys_jump_one l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar
