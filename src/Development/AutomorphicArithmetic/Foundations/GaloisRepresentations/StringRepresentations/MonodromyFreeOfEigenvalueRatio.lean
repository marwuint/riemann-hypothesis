import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.NormVEqPowResF

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem absSpace_smul {f : End ℂ V} {c : ℂ} (hc : c ≠ 0) {r : ℝ} {v : V} (hv : v ∈ absSpace (c • f) r) :
    v ∈ absSpace f (r / ‖c‖) := by
  refine (iSup₂_le fun α hα u hu => ?_ : absSpace (c • f) r ≤ absSpace f (r / ‖c‖)) hv
  refine Submodule.mem_iSup_of_mem (α / c) (Submodule.mem_iSup_of_mem (by rw [norm_div, hα]) ?_)
  rw [End.mem_eigenspace_iff] at hu ⊢
  rw [LinearMap.smul_apply] at hu
  rw [div_eq_inv_mul, mul_smul, ← hu, smul_smul, inv_mul_cancel₀ hc, one_smul]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

theorem Win.iso {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (e : a.Iso b) (hb : Win b S) : Win a S := by
  obtain ⟨e, e1, e2⟩ := e
  intro χ h0 r v hv hr hv0
  refine hb χ (fun u hu => ?_) r (e v) (fun s => by rw [← e1, hv s, map_smul])
    (map_absSpace_le e.toLinearMap (fun x => e1 _ x) r ⟨v, hr, rfl⟩) (e.map_ne_zero_iff.2 hv0)
  obtain ⟨u, rfl⟩ := e.surjective u
  rw [← e2, h0 u fun s => e.injective (by rw [e1, hu s, map_smul]), map_zero]

theorem Win.sum {a : WDRep h V} {b : WDRep h V'} {S : Set ℝ} (ha : Win a S) (hb : Win b S) : Win (a.sum b) S := by
  intro χ h0 r v hv hr hv0
  have hr' := (mem_absSpace_prodMap (a.ρ (frob h)) (b.ρ (frob h)) r v).1 hr
  by_cases h1 : v.1 = 0
  · refine hb χ (fun u hu => ?_) r v.2 (fun s => congrArg Prod.snd (hv s)) hr'.2 fun h2 => hv0 (Prod.ext h1 h2)
    exact congrArg Prod.snd (h0 (0, u) fun s => Prod.ext (by simp) (hu s))
  · refine ha χ (fun u hu => ?_) r v.1 (fun s => congrArg Prod.fst (hv s)) hr'.1 h1
    exact congrArg Prod.fst (h0 (u, 0) fun s => Prod.ext (hu s) (by simp))

theorem Win.mono {a : WDRep h V} {S T : Set ℝ} (ha : Win a S) (hS : S ⊆ T) : Win a T :=
  fun χ h0 r v hv hr hv0 => hS (ha χ h0 r v hv hr hv0)

theorem Win.tw {a : WDRep h V} {S : Set ℝ} (ha : Win a S) (s : ℝ) :
    Win (a.tw s) {r | r / ((normV w : ℕ) : ℝ) ^ s ∈ S} := by
  intro χ h0 r v hv hr hv0
  have e : ∀ u, EV (a.tw s) χ u ↔ EV a χ u := fun u => by simp [EV]
  have e2 : (a.tw s).ρ (frob h) = (qPow w s : ℂ) • a.ρ (frob h) := by simp [deg_frob]
  rw [e2] at hr
  have := ha χ (fun u hu => h0 u ((e u).2 hu)) _ v ((e v).1 hv) (absSpace_smul (qPow w s).ne_zero hr) hv0
  rwa [norm_qPow] at this

end UpperTheory.GalN
