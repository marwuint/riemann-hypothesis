import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Grid GlobalTheory.ChainFr
open scoped ENNReal

variable {D : D7}

theorem jm_not {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm (fun j => !(ε j)) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases h : a = b
  · subst h
    cases hε : ε a <;> simp [Formalism.REAL.Jm, hε]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_apply_ne _ h]

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j
  simp [gramAt, neg_gram]

def negFr (N : Node D) : Fr (neg N.V) where
  ε τ j := !(N.M.ε τ j)
  fr := N.M.fr
  fr_unit := N.M.fr_unit
  fr_gram τ := by
    rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, N.M.fr_gram τ, gramAt_neg]

theorem negFr_cart (N : Node D) : (negFr N).cart = cartS true N := by
  funext τ
  show (N.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun j => !(N.M.ε τ j)) * N.M.fr τ = -((N.M.fr τ)⁻¹ * Formalism.REAL.Jm (N.M.ε τ) * N.M.fr τ)
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul]

theorem thetaKernel_le_sobolev_mul_height_source {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeil ψ true S T χS χT ω) (μ : Measure (WO (neg S) T))
    (𝓓 : Set (WO (neg S) T)) (hμ : IsCovolOne (ratL T (neg S)) μ 𝓓) (U : AddSubgroup (WO (neg S) T))
    (hU : IsOpen (U : Set (WO (neg S) T))) :
    ∃ (d A : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ (neg S) T U, ∀ (g : GA D S) (h : GA D T),
      ‖thetaKO ω g h f‖ ≤ K * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight S g ^ A * GlobalTheory.Grow.height T h ^ A := by
  have hω' : IsWeilDatumO ψ (neg S) T χS χT (ω.toSgn true) := hω
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg S).rank T.rank
  obtain ⟨C, hC0, hC⟩ := (H (neg S) T rfl rfl).real ψ hθ hU
  refine ⟨d, A, C * 2 ^ A, by positivity, fun f hf g h => ?_⟩
  have hb := (hC χS χT (ω.toSgn true) hω' μ 𝓓 hμ f hf).2
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
    have e1 : (((ofSgn true S).symm (γ * g), h) : GA D (neg S) × GA D T) =
        ((ofSgn true S).symm γ, 1) * ((ofSgn true S).symm g, h) := by simp
    show (ω.toSgn true) ((ofSgn true S).symm (γ * g), h) f 0 = (ω.toSgn true) ((ofSgn true S).symm g, h) f 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hf.1)
  have hs : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
  have hgr : ∀ g, ‖thetaKO ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height T h ^ A) *
      GlobalTheory.Grow.height S g ^ A := fun g => by
    have := hb ((ofSgn true S).symm g) h
    refine this.trans_eq ?_
    show C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * (GlobalTheory.Grow.height S g * GlobalTheory.Grow.height T h) ^ A = _
    ring
  refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ω g h f) hinv hgr g).trans_eq ?_
  ring

theorem exists_sum_of_mem_fockSpan {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A : Fr V} {B : Fr W}
    {U : AddSubgroup (WO V W)} {g : WO V W → ℂ} (hg : g ∈ fockSpan ψ θ A B U) :
    ∃ (n : ℕ) (f : Fin n → (WO V W → ℂ)) (p : Fin n → PolF D W.rank V.rank),
      (∀ l, IsVacF ψ θ A B (f l)) ∧ g = ∑ l, ptF ψ θ A B (f l) (p l) := by
  obtain ⟨n, c, u, hu⟩ := Submodule.mem_span_set'.1 hg
  have hm : ∀ l, ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ (u l : WO V W → ℂ) = ptF ψ θ A B f₀ P :=
    fun l => (u l).2
  choose f₀ P hv _ he using hm
  refine ⟨n, f₀, fun l => c l • P l, hv, ?_⟩
  rw [← hu]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [he l]
  exact (map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb (f₀ l)) (c l) (P l)).symm

theorem isVacF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (negFr S) (Fr.ofModel T.M) f ↔ IsFinVec ψ θ true S T f := by
  unfold IsVacF IsFinVec
  rw [negFr_cart]
  rfl

theorem ptF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) (P : Pol S T) :
    ptF ψ θ (negFr S) (Fr.ofModel T.M) f P = fock ψ θ true S T f P := by
  unfold ptF fock
  rw [negFr_cart]
  rfl

end GlobalTheory.DownApprox
