import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLeOfAntilinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientField

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem eq_zero_of_cuspA_bot {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (j : Fin D.R.m)
    (hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (x : Fin (R.nW j) → D.what₂.LL) : x = 0 := by
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := fw.ks j
  have hWK : ∀ z ∈ (R.FW j).WK, z = 0 := fun z hz => by
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨z, hz⟩
    have hf0 : f = 0 := by
      have h1 : (f : T.R ((j : ℕ) + 1)) ∈ (⊥ : Submodule T.Q.c.F (T.R ((j : ℕ) + 1))) := hc ▸ f.2
      exact Subtype.ext ((Submodule.mem_bot _).1 h1)
    have := congrArg Subtype.val hf
    rw [hf0, map_zero] at this
    exact this.symm
  have h0 : Set.range b ⊆ {0} := by
    rintro _ ⟨k, rfl⟩; exact hWK _ (hb k)
  have : x ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hsp]; trivial
  have h2 := Submodule.span_mono h0 this
  simpa using h2

theorem adForm_smul {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (c : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (c • x) = sg0 D A c • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]

theorem adForm_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    adForm R i 0 = 0 := by
  unfold adForm
  rw [map_zero, map_zero]

theorem kerRat_framed (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {t : D.ntw.Tw} {j : Fin D.R.m}
    {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hH : RatHyp T Rl F κ v₀ O t j hV) (hph : ∀ k, Rl.phs k = 1)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) {χ ξR ω φ}
    (hK : KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {y : (Rl.cV j).W} (hy : InCoefLat Rl.toRealDat j h y)
    (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ) (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) :
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = singleSeries Rl.toRealDat j ω φ h y u := by
  obtain ⟨gramR, c0R, c0L, hFT, P, hPm, rfl⟩ := hy
  obtain ⟨ph, hph1, hphC⟩ := hS D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hH.laws hH.core.lev hH.core.grp hH.core.fam
    hH.core.models hH.core.thP hH.tieIn j hV hH.frame hH.std gramR c0R c0L hFT u hu
  have hRP : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := fun C hC _ => hphC C hC
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu ph hRP v χ ξR ω φ hK
    h hh P hPm
  have hph0 : ph ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1
  by_cases hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine ⟨0, ?_⟩
    rw [eq_zero_of_cuspA_bot hH.fw.some j hc x, adForm_zero] at hx
    rw [adForm_zero]
    funext g
    have e := congrFun hx.symm g
    have e2 : ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g = 0 := e
    exact ((mul_eq_zero.1 e2).resolve_left hph0).symm
  · obtain ⟨c, hcph⟩ := _root_.GlobalTheory.PhaseOneOnto.phase_mem_coefField hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu hph hc ph
      hph1 hRP
    refine ⟨c⁻¹ • x, ?_⟩
    rw [adForm_smul]
    funext g
    have e := congrFun hx g
    have e2 : adForm Rl.toRealDat j x (fun τ => u τ) g = ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g := e
    show sg0 D A3.A c⁻¹ * adForm Rl.toRealDat j x (fun τ => u τ) g = _
    rw [e2, map_inv₀, hcph, ← mul_assoc, inv_mul_cancel₀ hph0, one_mul]

end GlobalTheory.BigOn.Exp.SerBase
