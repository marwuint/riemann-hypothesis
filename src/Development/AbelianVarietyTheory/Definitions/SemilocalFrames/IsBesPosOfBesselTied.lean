import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OffCharsSeparates
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices (gramA gramInvA idemFin idemInf IsProbPair)
open GlobalTheory.BesselCompare (eMat)
open GlobalTheory.WeilTieCompare (kap kapT IsChange)
open scoped TensorProduct

namespace GlobalTheory.Per

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsUnitN (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (ν : Measure (NFlag B e))
    (𝓝 : Set (NFlag B e)) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B e) 𝓝 ν ∧ ν 𝓝 = 1

section Bessel

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def besFun (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ)
    (h : GA D A) (n : NFlag B d.e) : ℂ :=
  star (φ h) * F ((n : GA D B) * s h * (d.y : GA D B)) * star (besChar ψ d (n : GA D B))

def besPer (ψ : AddChar (AF D.host.F) ℂ) (d : BesDat A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure (NFlag B d.e)) (𝓝 : Set (NFlag B d.e)) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : ℂ :=
  ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ d s φ F h n ∂ν ∂μ

end Bessel

structure IsNegLine (L : HSp D) : Prop where
  rank_one : L.rank = 1
  sigOK : L.SigOK
  neg : ∀ τ, L.sig τ = (0, 1)

structure FJDat (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  line : IsNegLine L
  isom : HSpace.IsIsomEmb A B ι

  ρ : ℕ
  codim : A.rank + 2 * ρ = B.rank

  e : Fin ρ → B.V

  f : Fin ρ → B.V
  ee : ∀ i j, B.hD (e i) (e j) = 0
  ff : ∀ i j, B.hD (f i) (f j) = 0
  ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0
  eA : ∀ i x, B.hD (e i) (ι x) = 0
  fA : ∀ i x, B.hD (f i) (ι x) = 0

  β : Fin (ρ - 1) → D.host.E
  β_ne : ∀ i, β i ≠ 0

  c : D.host.E
  c_ne : c ≠ 0

def coefH (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (m : Measure (WA V W) × Set (WA V W)) (f : WA V W → ℂ)
    (u : WA V W) : ℂ :=
  ∫ w in m.2, Heisenberg₂ ψ V W u f w * star (f w) ∂m.1

section Comparison₂

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem isAniso_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) : IsAniso V := by
  refine (BesselCompare.isAniso_iff V).2 fun v hv => ?_
  by_contra hne
  have h1 := hs D.host.φ₀
  rw [hp] at h1
  have h2 := Formalism.UG.P.stdform_sig_pos _ h1 (fun k => D.host.φ₀ (BesselCompare.co V v k)) fun e => hne (by
    apply V.frame.repr.injective
    refine Finsupp.ext fun k => ?_
    simpa [BesselCompare.co] using congrFun e k)
  have hc := D.host.isCMField_hostE
  have h3 : ∀ a : D.host.E, D.host.φ₀ (star a) = starRingEnd ℂ (D.host.φ₀ a) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀
  have h4 := congrArg (fun a => (D.host.φ₀ a).re) ((BesselCompare.hT_co V v v).symm.trans hv)
  simp only [map_sum, map_mul, h3, map_zero, Complex.zero_re] at h4
  exact h2.ne' h4

end Comparison₂

end GlobalTheory.Per

end
