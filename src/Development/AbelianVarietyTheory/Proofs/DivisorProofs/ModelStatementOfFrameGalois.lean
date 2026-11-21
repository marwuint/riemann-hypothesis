import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgChainBStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMapExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealsMeetingSubspaceCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientDualWeylEmbedsHighestWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineLatticeLinkOfBlockDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasBlocksOfSystemOccursInBlockPart
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoeffRingPrimeNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifDvd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization GlobalTheory.ExpModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lift_subquot {A V : Type} [Ring A] [AddCommGroup V] [Module A V] (S : Submodule A V) (E : Submodule A (V ⧸ S))
    (N' : Submodule A E) : ∃ (U : Submodule A V) (π : U →ₗ[A] (E ⧸ N')), Function.Surjective π ∧ ∀ x : U, (x : V) ∈ S → π x = 0 := by
  let g : E.comap S.mkQ →ₗ[A] E := (S.mkQ.domRestrict (E.comap S.mkQ)).codRestrict E (fun x => x.2)
  refine ⟨E.comap S.mkQ, N'.mkQ ∘ₗ g, fun z => ?_, fun x hx => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective S a
    have hvU : v ∈ E.comap S.mkQ := by rw [Submodule.mem_comap, hv]; exact a.2
    have hg : g ⟨v, hvU⟩ = a := Subtype.ext hv
    exact ⟨⟨v, hvU⟩, congrArg N'.mkQ hg⟩
  · have hg : g x = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero S).2 hx)
    exact (congrArg N'.mkQ hg).trans (map_zero _)

set_option maxHeartbeats 800000 in

theorem winputs_of_simple {ι : Type} [DecidableEq ι] (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (W : Wts ι) (X : HidaSetting ι P.Nr W.lam) (l : ℕ) (ϖ : X.O)
    (n₀ : ℕ) (e : ι → (Fin P.Nr → ℕ) → X.A) (hfin : Finite (X.O ⧸ Ideal.span {(l : X.O)})) (hd : (l : X.O) ∣ ϖ ^ n₀)
    (hA : X.FrameA e) (hS : HeckeStable X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam))
    (hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module X.O Gm] [Module X.A Gm] [IsScalarTower X.O X.A Gm], IsSimpleModule X.A Gm →
      (∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] Gm), Function.Surjective π ∧
        ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0) →
      ∃ (_ : Module X.T (Forms X.O X.Γ X.jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat X.O X.Γ X.jK X.T (NablaT X.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule X.S (Forms X.O X.Γ X.jK Gm)) → ∀ τ, LatticeLink P W l τ (hw τ))) :
    WInputsLink P W X l := by
  have hsq : ∀ μ : SimpIx X ϖ, ∃ (U : Submodule X.A (NablaT X.O P.Nr W.lam)) (π : U →ₗ[X.A] SimpMod X ϖ μ), Function.Surjective π ∧
      ∀ (x : U) (y : NablaT X.O P.Nr W.lam), (x : NablaT X.O P.Nr W.lam) = ϖ • y → π x = 0 := by
    intro μ
    obtain ⟨U, π, h1, h2⟩ := exists_lift_subquot _ μ.1 μ.2.1
    exact ⟨U, π, h1, fun x y hxy => h2 x ⟨y, hxy⟩⟩
  have h := fun μ : SimpIx X ϖ => hQ (SimpMod X ϖ μ) μ.2.2 (hsq μ)
  choose mT hw h1 h2 h3 using h
  exact ⟨ϖ, n₀, e, SimpIx X ϖ, SimpMod X ϖ, fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, mT, hw, hfin, hd, hA, ⟨hS, h1⟩, ⟨fun Gm _ _ _ hq => exists_simpMod Gm hq, h2⟩,
    fun μ _ hn τ _ => h3 μ hn τ⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem winputs_frame : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), W.Ok P → (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))] [IsScalarTower F.O F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK (NablaT F.O P.Nr W.lam))], F.IsHecke W.lam jK (NablaT F.O P.Nr W.lam) → Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) → ¬ IsUnit ((l : ℕ) : F.O) → ∀ (m : Ideal F.T) [hm : m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → haveI := hm.isPrime; WInputsLink P (reFr W fr cjj) (F.setting W.lam jK m) l := by
  intro E Ω _ _ _ _ _ _ hCheb l _ ι _ _ inc fr cjj P W hW hlink F hF Bk hG jK hJ _ _ hH hfin hnu m hm θ0 h0e h0b h0o
  obtain ⟨ϖ, n₀, hϖ, hϖl, hlϖ⟩ := exists_unif_dvd F.O l (Fact.out : l.Prime).ne_zero hnu
  have hanti : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
  choose e0 he0 hu0 using GlobalTheory.ExpFrame.exists_unique_isProj F.O P.Nr ι W.lam
  let e : ι → (Fin P.Nr → ℕ) → alg F.O P.Nr W.lam := fun τ w => ⟨e0 τ w, Algebra.subset_adjoin (Or.inr ⟨τ, w, he0 τ w⟩)⟩
  have hQ : ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm]
      [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm], IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm →
      ∃ (_ : Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) (hw : ι → Fin P.Nr → ℕ),
        HeckeNat F.O (A := alg F.O P.Nr W.lam) F.Γ jK F.T (NablaT F.O P.Nr W.lam) Gm ∧ (∀ τ, ∃ z : Gm, e τ (hw τ) • z ≠ 0) ∧
        (¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) →
          ∀ τ, LatticeLink P (reFr W fr cjj) l τ (hw τ)) := by
    intro Gm _ _ _ _ hs hq
    obtain ⟨mT, _, hHG⟩ := GlobalTheory.ExpFrame.HeckeMod.hecke_module l ι P.Nr F W.lam jK hF hJ Gm
    obtain ⟨mu, hmu, hemb⟩ := _root_.GlobalTheory.HighWt.simpleSubquot_embeds F.O P.Nr ι W.lam ϖ hϖ hanti Gm hs hq
    refine ⟨mT, fun τ => res P.Nr (mu τ), (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK Gm hH hHG).2, fun τ => ?_, fun hn =>
      GlobalTheory.T.latticeLink_of_surviving_simple_subquotient E Ω hCheb l ι inc fr cjj P W hlink F hF Bk hG jK hJ ϖ hϖ hϖl hanti Gm hHG hs hq mu
        (fun τ => ⟨(hmu τ).1, (hmu τ).2.1, (hmu τ).2.2.1⟩) hemb m θ0 h0e h0b h0o hn⟩
    obtain ⟨e', z, hp, hz⟩ := (hmu τ).2.2.2
    have hee : e τ (res P.Nr (mu τ)) = e' := Subtype.ext (hu0 τ _ _ hp).symm
    exact ⟨z, hee ▸ hz⟩
  haveI := hm.isPrime
  exact winputs_of_simple P (reFr W fr cjj) (F.setting W.lam jK m) l ϖ n₀ e hfin hlϖ
    ⟨GlobalTheory.ExpFrame.alg_chainB_stable F.O P.Nr ι W.lam, fun τ w => he0 τ w⟩
    (GlobalTheory.T.heckeStable_of_heckeFrame_polynomial_action l ι P.Nr F W.lam jK (NablaT F.O P.Nr W.lam) hH hH).1
    (fun Gm i1 i2 i3 i4 => @hQ Gm i1 i2 i3 i4)

end GlobalTheory.ExpModel

end
