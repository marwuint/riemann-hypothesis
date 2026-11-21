import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopLift

open GlobalTheory.Mem.ColAd Filter Topology

section Comp

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem finN_mem_UPts (g : GA D V) : finN V hn g ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  exact GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V g)

theorem finN_eq (g : GA D V) (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (h : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom V g)).1 i j = y.1 (finCongr hn i) (finCongr hn j)) : finN V hn g = y := by
  subst hn
  exact Units.ext (Matrix.ext h)

theorem infN_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) (atTau θ V τ g) ρ : Matrix (Fin n) (Fin n) ℂ) =
      (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  have h : IsAtTau θ V τ g (atTau θ V τ g) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  show Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ g) = Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ
  by_cases c : ρ = τ
  · subst c
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne c]
    exact h.2.2 ρ c

end Comp

section Main

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (θ : InfFam D)

def finPt (h : GA D D.sp.X') : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨finN D.sp.X' (rankP D) h, finN_mem_UPts D.sp.X' (rankP D) h⟩

theorem finPt_mul (h k : GA D D.sp.X') : (finPt (h * k)).1 = (finPt h).1 * (finPt k).1 := map_mul (finN D.sp.X' (rankP D)) h k

abbrev infPt : GA D D.sp.X' →* (D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) := infN θ D.sp.X' (rankP D) (Equiv.refl _)

theorem finPt_of_hasMat {h : GA D D.sp.X'} {y} (hh : HasMat h y) : (finPt h).1 = y := finN_eq _ (rankP D) h y hh.2

variable {g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ}

theorem finPt_mul_inf (h : GA D D.sp.X') {k : GA D D.sp.X'} (hk : k ∈ GinfC D.sp.X') : finPt (h * k) = finPt h := by
  refine Subtype.ext ?_
  rw [finPt_mul, show (finPt k).1 = 1 from finN_of_inf (rankP D) hk, mul_one]

theorem infPt_of_fin {k : GA D D.sp.X'} (hk : k ∈ GfC D.sp.X') : infPt θ k = 1 := infN_of_fin θ (rankP D) _ hk

variable (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ)

end Main

end GlobalTheory.Core.Rk.TopLift

end
