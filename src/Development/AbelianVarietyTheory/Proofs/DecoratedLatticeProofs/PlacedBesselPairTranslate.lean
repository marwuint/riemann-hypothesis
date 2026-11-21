import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairLattice

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CentralUnitGen

theorem scalar_keeps {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (Λ : Submodule S (Fin n → R)) (w : Fin n → R)
    (Mt Mt' Mk Mki : Matrix (Fin n) (Fin n) R) (c c' : R)
    (h1 : Mt = (c • (1 : Matrix (Fin n) (Fin n) R)) * Mt' * Mk) (h2 : (c' * c) • (1 : Matrix (Fin n) (Fin n) R) = 1)
    (hkk : Mk * Mki = 1)
    (hk : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mk y ∈ Λ) (hki : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mki y ∈ Λ)
    (hw : ∀ c0 : R, ((∃ x ∈ Λ, Matrix.mulVec Mt x = c0 • w) ↔ c0 ∈ S) ∧ ((∃ x ∈ Λ, Matrix.mulVec Mt' x = c0 • w) ↔ c0 ∈ S)) :
    ∀ y, y ∈ Λ ↔ Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y ∈ Λ := by
  have e2 : Mt' * Mk = (c' • (1 : Matrix (Fin n) (Fin n) R)) * Mt := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, Matrix.one_mul]
  have hcI : c ∈ S := by
    obtain ⟨x', hx', ex'⟩ := ((hw 1).2).2 (one_mem _)
    refine ((hw c).1).1 ⟨Matrix.mulVec Mki x', (hki x').1 hx', ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.mul_assoc, Matrix.mul_assoc, hkk, Matrix.mul_one, ← Matrix.mulVec_mulVec, ex', one_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc'I : c' ∈ S := by
    obtain ⟨x, hx, ex⟩ := ((hw 1).1).2 (one_mem _)
    refine ((hw c').2).1 ⟨Matrix.mulVec Mk x, (hk x).1 hx, ?_⟩
    rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec, ex, one_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro y
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hy
    exact Λ.smul_mem ⟨c, hcI⟩ hy
  · intro hy
    have h3 := Λ.smul_mem ⟨c', hc'I⟩ hy
    have e3 : (c' * c) • y = y := by
      have := congrArg (fun A => Matrix.mulVec A y) h2
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using this
    rw [← e3, mul_smul]
    exact h3

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.CentralUnitGen

theorem proj_mem_center {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : GlobalTheory.AdelicU.GAd σ J}
    (hg : g ∈ Subgroup.center (GlobalTheory.AdelicU.GAd σ J)) : GlobalTheory.AdelicU.proj σ J v g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc σ J v) := by
  refine Subgroup.mem_center_iff.2 fun x => ?_
  have e := congrArg (GlobalTheory.AdelicU.proj σ J v) (Subgroup.mem_center_iff.1 hg (GlobalTheory.AdelicU.emb σ J v x))
  rwa [map_mul, map_mul, GlobalTheory.AdelicU.proj_emb_self] at e

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop

end
