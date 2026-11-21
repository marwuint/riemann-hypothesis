import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.ConjugacyTypeUnfolding
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CexpTwoPiINegInvNatSmulAddStar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RangeBesselAnisotropicEmbeddingEqSecondModelSubg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramEqOfInst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarEqHostConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.BasicNotions Formalism.L2.Theta GlobalTheory.MixPer GlobalTheory.MixModel MeasureTheory
  GlobalTheory.Core.Mi GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyTypeUnfolding Formalism.L2.SG.InstExistsPf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Matrix

noncomputable section

namespace GlobalTheory.Core.Mi.PerCmp

variable {D : D7} {X : HidaSetting.HidaSetting D} {h : X.B.I = instOf D} {u : D.what₂.Word}
  {V₀ A L : HSp D} {d : HypDec (D.sp.Y 0) V₀ D.R.rS} {o : OrthDec V₀ A L}
  {ζ : Fin L.rank → D.host.E} {lam : D.host.E}

theorem hyp_linIndep {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    LinearIndependent D.host.E d.e.transpose := by
  have h1 : Function.Injective d.e.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (d.e'.conjTranspose * HSpace.gram S).mulVec v) hxy
    simpa [Matrix.mulVec_mulVec, d.e'e] using this
  exact Matrix.mulVec_injective_iff.mp h1

structure Match {ψ : AddChar (AF ↥D.host.F) ℂ} (B : SBes X h u ψ A)
    (hF : IsFrame X h u d o ζ) (ψ₀ : AddChar (AF ↥D.host.F) ℂ) (ν : Measure (flagN d))
    (𝓝 : Set (flagN d)) : Prop where
  emb : embA B.d B.o = embA d o
  per : ∀ φ f, B.lev.per ψ φ f = besPer ψ₀ (thetaS D) d o ζ B.vA.μ B.vA.𝓕 ν 𝓝 φ f

theorem besPer_domN {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) {ψ : AddChar (AF ↥D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (θ : D.host.E) (μ 𝓕) (ν : Measure (flagN d)) (hν : ν.IsHaarMeasure) {𝓝 𝓝' : Set (flagN d)}
    (h𝓝 : IsFundamentalDomain (NFlagQ S d.e) 𝓝 ν) (h𝓝' : IsFundamentalDomain (NFlagQ S d.e) 𝓝' ν)
    (φ : GA D A → ℂ) (f : GA D S → ℂ) (hf : ∀ γ ∈ GQ S, ∀ g, f (γ * g) = f g) :
    besPer ψ θ d o ζ μ 𝓕 ν 𝓝 φ f = besPer ψ θ d o ζ μ 𝓕 ν 𝓝' φ f := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : Countable (NFlagQ S d.e) := by
    have hinj : Function.Injective
        (fun x : NFlagQ S d.e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  unfold besPer
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine h𝓝.setIntegral_eq h𝓝' fun γ n => ?_
  have hγ : ((γ : flagN d) : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 γ.2
  change besFun ψ θ d o ζ φ f a ((γ : flagN d) * n) = _
  simp only [besFun, Subgroup.coe_mul]
  rw [psiBes_mul d ψ θ _ γ.1.2 n.2, GlobalTheory.CharLaws.psiBes_rat ψ d hψ.2.2.1 θ _ hγ, one_mul,
    mul_assoc ((γ : flagN d) : GA D S), hf _ hγ]

theorem besPer_domA {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF ↥D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {𝓕 : Set (GA D B.A)} (h𝓕 : IsFundamentalDomain (GQ B.A) 𝓕 B.vA.μ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ B.vA.μ 𝓕 B.vN.ν B.vN.𝓝 φ f = B.per ψ φ f := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  exact h𝓕.setIntegral_eq B.vA.fund fun γ x => Shift.inner_left B ψ hψ φ f hφ hf γ.2 x

end GlobalTheory.Core.Mi.PerCmp
