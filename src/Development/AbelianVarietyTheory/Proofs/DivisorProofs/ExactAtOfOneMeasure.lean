import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.CovTop.MeasRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem sgAt_mk_eq {K : Type} [Field K] (σ₀ σ : K →+* ℂ) :
    sgAt σ₀ (InfinitePlace.mk σ) = σ ∨ sgAt σ₀ (InfinitePlace.mk σ) = (starRingEnd ℂ).comp σ := by
  have hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
    RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
  unfold sgAt
  split_ifs with h
  · rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact Or.inl h1.symm
    · right; rw [← h1, hc]
  · rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact Or.inl h1
    · right; rw [h1, hc]

theorem phiC_congr {T : CoreJ D} {j : ℕ} {σ₁ σ₂ : T.Q.c.F →+* ℂ} (e : σ₁ = σ₂) {W : Formalism.BasicNotions.TH.HSp D}
    (h₁ : T.V j σ₁ = W) (h₂ : T.V j σ₂ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T h₁ a f = phiC T h₂ a f := by
  subst e; rfl

end GlobalTheory.CovTop.MeasRd

namespace GlobalTheory.CovTop.MeasRd

end GlobalTheory.CovTop.MeasRd
