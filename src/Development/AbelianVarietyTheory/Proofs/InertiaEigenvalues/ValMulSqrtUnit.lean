import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEmbeddingGeneratorEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOne
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitOverP

theorem val_eq_one_of_pow (A : ValuationSubring ℂ) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (h : A.valuation (z ^ m) = 1) :
    A.valuation z = 1 := by
  rw [map_pow] at h
  exact ((pow_eq_one_iff).1 h).resolve_right hm

theorem exists_gen {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 K, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 K))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 K)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

end GlobalTheory.UnitOverP

namespace GlobalTheory.UnitOverP

end GlobalTheory.UnitOverP
