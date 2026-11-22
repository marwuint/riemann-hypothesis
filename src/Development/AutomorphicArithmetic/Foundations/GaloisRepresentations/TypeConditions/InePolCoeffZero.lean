import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InePolOfUnr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixCharpolySmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfIsPlaceOver
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.LeviInductionForms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.L2.Host Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.HeightCounting GlobalTheory.SmGL GlobalTheory.SatakeFlip GlobalTheory.LocGL
open GlobalTheory.Mem.Chr hiding HChar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

def SepW (y : WD h) : Prop := y.tame ∧ ∃ s ∈ Ine (F := E) B, (y.inePol s).Separable

theorem SepW.ncW {y : WD h} (k : SepW y) (ht : thr w y.lpDim = 2) : NcW y := by
  obtain ⟨k1, s, hs, k2⟩ := k
  refine ⟨(WD.tame_iff_inePol y).1 k1, WD.noMonodromy_of_inertia_separable_charpoly E Ω B w h y s hs k2, fun γ hγ hc z hz => ?_⟩
  exfalso
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  rw [ht, WD.inePol_of_mem_Ine _ hγ, WD.charPol_mk] at hz
  rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
  let U := End.eigenspace (a.ρ (ineIncl h ⟨γ, hγ⟩)) z
  let K : Subgroup (Ine (F := E) B) :=
    { carrier := {σ | ∃ c : ℂ, ∀ v ∈ U, a.ρ (ineIncl h σ) v = c • v}
      one_mem' := ⟨1, fun v _ => by simp⟩
      mul_mem' := fun {x y} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨d * c, fun v hv => by
        rw [map_mul, map_mul, End.mul_apply, hd v hv, map_smul, hc v hv, smul_smul]⟩
      inv_mem' := fun {x} ⟨c, hc⟩ => ⟨c⁻¹, fun v hv => by
        have e : a.ρ (ineIncl h x⁻¹) (a.ρ (ineIncl h x) v) = v := by
          rw [← End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, End.one_apply]
        rw [hc v hv, map_smul] at e
        by_cases h0 : c = 0
        · rw [h0, zero_smul] at e; rw [← e]; simp
        · rw [← e, smul_smul, inv_mul_cancel₀ h0, one_smul, e]⟩ }
  have hop : IsOpen (K : Set (Ine (F := E) B)) :=
    K.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (IsOpen.mem_nhds a.smooth (by
      show a.ρ (ineIncl h 1) = 1
      rw [map_one, map_one])) fun σ hσ => ⟨1, fun v _ => by
      have : a.ρ (ineIncl h σ) = 1 := hσ
      rw [this]; simp⟩)
  have hK : IsClosed ((K.map (Ine (F := E) B).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine B).isClosedEmbedding_subtypeVal.isClosedMap _ (K.isClosed_of_isOpen hop)
  have hle : Subgroup.closure (insert γ (Wild E B : Set (G E Ω))) ≤ K.map (Ine (F := E) B).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ⟩, ⟨z, fun v hv => End.mem_eigenspace_iff.1 hv⟩, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, ⟨1, fun v _ => by rw [k1 _ hu]; simp⟩, rfl⟩
  obtain ⟨u, ⟨c, hu⟩, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hc hs)
  obtain rfl : u = ⟨s, hs⟩ := Subtype.ext e
  have h1 : finrank ℂ U = (a.ρ (ineIncl h ⟨γ, hγ⟩)).charpoly.rootMultiplicity z := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
  have h2 : finrank ℂ U ≤ (a.ρ (ineIncl h ⟨s, hs⟩)).charpoly.rootMultiplicity c := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq, (a.semisimple _).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace]
    exact Submodule.finrank_mono fun v hv => End.mem_eigenspace_iff.2 (hu v hv)
  have h3 := rootMultiplicity_le_one_of_separable k2 c
  omega

theorem SepW.dual {y : WD h} (k : SepW y) : SepW y.lpDual := by
  obtain ⟨k1, s, hs, k2⟩ := k
  obtain ⟨n, a, rfl⟩ := y.exists_rep
  rw [WD.tame_mk] at k1
  refine ⟨?_, s⁻¹, inv_mem hs, ?_⟩
  · rw [WD.lpDual_mk, WD.tame_mk]
    intro σ hσ
    rw [WDRep.dual_ρ, k1 σ⁻¹ (inv_mem hσ)]
    rfl
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.lpDual_mk, WD.inePol_of_mem_Ine _ (inv_mem hs), WD.charPol_mk, WDRep.dual_ρ, LabDual.charpoly_dualMap]
    convert k2 using 3
    exact Subtype.ext (inv_inv s)

theorem SepW.transport {B' : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E)} {h' : IsPlaceOver B' w'} {n : ℕ}
    (c : Ω ≃+* Ω) (τ : E ≃+* E) (hτ : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (τ x)) (hc : ∀ y, y ∈ B' ↔ c y ∈ B)
    {b' : WDRep h' (Fin n → ℂ)} {b : WDRep h (Fin n → ℂ)}
    (e : ∀ (σ' : Weil h') (σ : Weil h), (∀ z, c ((σ' : G E Ω) z) = (σ : G E Ω) (c z)) → b'.ρ σ' = b.ρ σ)
    (k : SepW (WD.mk b)) : SepW (WD.mk b') := by
  obtain ⟨k1, s, hs, k2⟩ := k
  rw [WD.tame_mk] at k1
  have hc' : ∀ y, y ∈ B ↔ c.symm y ∈ B' := fun y => by rw [hc, c.apply_symm_apply]
  have hs' := ConjTransport.conjG_mem_Ine c.symm τ.symm (ConjTransport.symm_alg c τ hτ) hc' hs
  refine ⟨(WD.tame_mk _).2 fun σ hσ => ?_, _, hs', ?_⟩
  · have hw : ConjTransport.conjG c τ hτ σ ∈ Wild E B := ConjTransport.conjG_mem_wild c τ hτ hc hσ
    rw [e σ (ineIncl h ⟨_, Wild_le_Ine hw⟩) fun z => (ConjTransport.conjG_apply_c c τ hτ _ z).symm]
    exact k1 _ hw
  · rw [WD.inePol_of_mem_Ine _ hs, WD.charPol_mk] at k2
    rw [WD.inePol_of_mem_Ine _ hs', WD.charPol_mk, e _ (ineIncl h ⟨s, hs⟩) fun z => c.apply_symm_apply _]
    exact k2
end

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Sep {w : PlE H} (y : A.LP w) : Prop := Tm N A y ∧ ∃ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol y s).Separable

variable {N A}

theorem tm_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Tm N A y ↔ (T.e w y).tame := by
  rw [WD.tame_iff_inePol]
  refine ⟨fun k σ hσ => ?_, fun k σ hσ hw => ?_⟩
  · rw [← T.inePol w y σ (Wild_le_Ine hσ), T.dim]
    exact k σ (Wild_le_Ine hσ) hσ
  · rw [T.inePol w y σ hσ, ← T.dim]
    exact k σ hw

theorem sep_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (y : A.LP w) : Sep N A y ↔ SepW (T.e w y) :=
  and_congr (tm_iff T y) (exists_congr fun s => and_congr_right fun hs => by rw [T.inePol w y s hs])

theorem nc_of_sep (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (ht : thr w (A.lpDim y) = 2) (h : Sep N A y) :
    Nc N A y :=
  (nc_iff T y).2 (((sep_iff T y).1 h).ncW (by rwa [T.dim]))

theorem sep_char (hLP : Formalism.MainNotions.SumRepresentations.At.TieLP N A) {w : PlE H} {y c : A.LP w} (hc : A.lpDim c = 1) (tc : Tm N A c)
    (h0 : ∀ s ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol c s).coeff 0 ≠ 0) (h : Sep N A y) : Sep N A (A.lpChar y c) := by
  obtain ⟨k1, s, hs, k2⟩ := h
  refine ⟨fun σ hσ hw => ?_, s, hs, ?_⟩
  · have e : A.inePol c σ = X - C 1 := by rw [tc σ hσ hw, hc]; simp
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one, k1 σ hσ hw, A.lpDim_char _ _ hc]
  · obtain ⟨m1, m2⟩ := inePol_monic hLP c s hs
    rw [hc] at m2
    have e : A.inePol c s = X - C (-(A.inePol c s).coeff 0) := by
      rw [C_neg, sub_neg_eq_add]; exact m1.eq_X_add_C m2
    have hz : -(A.inePol c s).coeff 0 ≠ 0 := neg_ne_zero.2 (h0 s hs)
    rw [((hLP w y y c c 0 hc hc).2.2.2.2.2 s hs).2 _ e]
    obtain ⟨n1, -⟩ := inePol_monic hLP y s hs
    have sp := IsAlgClosed.splits (A.inePol y s)
    refine (nodup_roots_iff_of_splits ((monic_scaleRoots_iff _).2 n1).ne_zero (IsAlgClosed.splits _)).1 ?_
    rw [roots_scaleRoots _ hz.isUnit]
    exact (nodup_roots k2).map (mul_right_injective₀ hz)
end

theorem inePol_coeff_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (c : A.LP w) (s) (hs : s ∈ Ine (F := H.E) (N.plOm.1 w)) :
    (A.inePol c s).coeff 0 ≠ 0 := by
  rw [T.inePol w c s hs, WD.inePol_of_mem_Ine _ hs]
  obtain ⟨n, a, e⟩ := (T.e w c).exists_rep
  rw [← e, WD.charPol_mk]
  intro h0
  have hu : IsUnit (a.ρ (ineIncl (N.plOm.2 w) ⟨s, hs⟩)) := (Group.isUnit _).map a.ρ
  have hd := (LinearMap.isUnit_iff_isUnit_det _).1 hu
  rw [LinearMap.det_eq_sign_charpoly_coeff, h0, mul_zero] at hd
  exact not_isUnit_zero hd

end UpperTheory.GalS
