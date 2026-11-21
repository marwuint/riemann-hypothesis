import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsThetaPOfIntegrable

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace Topology ComplexOrder
open GlobalTheory.GalLift

namespace GlobalTheory.ConjThetaIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjVal_one {D : D7} {σ : D.what₂.LL →+* ℂ} {a b : ℂ} (h : ConjVal σ a b) (ha : a = 1) : b = 1 := by
  obtain ⟨y, h1, h2⟩ := h
  have : y = 1 := D.what₂.embLL.injective (by rw [h1, ha, map_one])
  rw [← h2, this, map_one]

theorem ext_continuous {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (χ' : (levEnv V β L).J →* ℂˣ) (hχ : ∀ k, (levEnv V β L).χ k = 1 → χ' k = 1)
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J χ') : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1
    ((GlobalTheory.ThetaIntegrand.eventually_level V β L).mono fun _ h => h.elim fun hk h1 => ⟨hk, hχ _ h1⟩) hf

theorem IsThetaP₂ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] (Bridge.Gf S → c.W))
    (he : ∀ x, e x ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (io : TK →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) :
    ∃ thP, Lift.IsThetaP μ 𝓕 (fun g h φ => thetaKO om h g φ) (fun P => pt P) io (LinearMap.range (c.ext ∘ₗ e)) thP := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine GlobalTheory.ThetaIntegralLinear.exists_isThetaP_of_integrable μ 𝓕
    (fun g h => LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0 ∘ₗ om (h, g)) pt io _ ?_
  rintro ⟨_, x, rfl⟩ v g
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io v)
    (fun w => hpt _) _ (ext_continuous c hc β L χ' hχ (he x)) (GlobalTheory.ThetaIntegrand.ext_invariant c (he x)) μ 𝓕 hμ.1.1 hμ.2 g

end GlobalTheory.ConjThetaIntegral

end
