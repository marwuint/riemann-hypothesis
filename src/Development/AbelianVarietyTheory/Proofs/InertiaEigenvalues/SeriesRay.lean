import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRayFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowestWeightVectorsAtRows
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩
  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)
  · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

section First

variable {T R i κ}

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}

variable (u c0 ka J) in

structure Dict : Prop where
  norm : ‖ka‖ = 1
  rat : ∀ k : Subfield ℂ, (inC T.Q.c).fieldRange ≤ k → ∀ v : VsV D i ℂ,
    (∀ m, MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) ↔ ∀ d, MvPolynomial.coeff d (J v) ∈ k
  eq : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v,
    IntegralSeries.fock R i (R.BV i) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • IntegralSeries.fock R i (fun _ => 1) f (J v)

end First

end GlobalTheory.Cmp.SeriesRay
