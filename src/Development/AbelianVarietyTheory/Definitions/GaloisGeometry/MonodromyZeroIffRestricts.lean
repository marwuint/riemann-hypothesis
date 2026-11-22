import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsPolarizedOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.Model

section Tower

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}

theorem ineTriv_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    IneTriv (WD.mk a) ↔ ∀ τ : Ine (F := K) A, a.ρ (ineIncl h τ) = 1 := by
  refine forall_congr' fun τ => ?_
  rw [WD.charPol_mk, WD.lpDim_mk]
  refine ⟨fun e => ?_, fun e => by rw [e, LinearMap.charpoly_one]⟩
  have h1 := LinearMap.aeval_self_charpoly (a.ρ (ineIncl h τ))
  rw [e, map_pow, map_sub, Polynomial.aeval_X, map_one] at h1
  have h2 : Module.End.IsSemisimple (a.ρ (ineIncl h τ) - 1) := by
    have := (Module.End.isSemisimple_sub_algebraMap_iff (f := a.ρ (ineIncl h τ)) (μ := (1 : ℂ))).2 (a.semisimple _)
    simpa using this
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ h2)

theorem unr_iff (x : WD h) : x.unr ↔ x.mono0 ∧ IneTriv x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.unr_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, ineTriv_mk]; rfl

variable [Algebra K L] [IsScalarTower K L Ω]

end Tower

end GlobalTheory.AboveL.Model

end
