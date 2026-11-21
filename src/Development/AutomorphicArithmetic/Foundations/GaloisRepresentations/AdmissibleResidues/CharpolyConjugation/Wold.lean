import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem norm_one {x : WD h} {t : ℝ} (ht : (x.lpTw t).tempered) (h0 : x.mono0) {g : ↥(Weil h)}
    (hg : deg g = 1) {α : ℂ} (hα : α ∈ (x.lpTw t).eig g) : ‖α‖ = 1 := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.tempered_mk] at ht
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [WD.lpTw_mk, WD.eig_mk] at hα
    have top := ht.norm_eq_one (by simpa using h0) hg
    have hroot := (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue ((a.tw t).ρ g) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    by_contra hne
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have hind := Module.End.eigenspaces_iSupIndep ((a.tw t).ρ g)
    have hle : absSpace ((a.tw t).ρ g) 1 ≤ ⨆ (μ : ℂ) (_ : μ ≠ α), Module.End.eigenspace ((a.tw t).ρ g) μ := by
      refine iSup_le fun μ => iSup_le fun hμ => ?_
      exact le_iSup₂_of_le μ (fun e => hne (e ▸ hμ)) le_rfl
    rw [top] at hle
    have hd := (hind α).le_bot ⟨hv.1, hle Submodule.mem_top⟩
    exact hv.2 (by simpa using hd)

private theorem win {x : WD h} {t : ℝ} (ht : (x.lpTw t).tempered) (h0 : x.mono0) {g : ↥(Weil h)}
    (hg : deg g = 1) {α β : ℂ} (hα : α ∈ x.eig g) (hβ : β ∈ x.eig g) : ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖ := by
  set c : ℂ := ((normV w : ℕ) : ℂ) ^ ((t : ℝ) : ℂ) with hc
  have mem : ∀ z ∈ x.eig g, ‖z‖ * ‖c‖ = 1 := fun z hz => by
    rw [← norm_mul]
    exact norm_one ht h0 hg (by rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hg]; exact Multiset.mem_map_of_mem _ hz)
  have e1 := mem α hα
  have e2 := mem β hβ
  have hc0 : ‖c‖ ≠ 0 := fun e => by rw [e, mul_zero] at e1; exact zero_ne_one e1
  have heq : ‖α‖ = ‖β‖ := mul_right_cancel₀ hc0 (e1.trans e2.symm)
  have hb : 0 < ‖β‖ := by
    rcases (norm_nonneg β).eq_or_lt with e | e
    · rw [← e, zero_mul] at e2; exact absurd e2 zero_ne_one
    · exact e
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  rw [heq]
  nlinarith

end

