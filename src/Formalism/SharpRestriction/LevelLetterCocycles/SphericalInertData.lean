import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

structure Pend : Prop where
  infG_card : ∀ {a} (π : D.naut.CG a) τ, Multiset.card (D.naut.infG π τ) = a
  ralg_iff : ∀ {a} (π : D.naut.CG a), D.naut.ralg π ↔
    ∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ x ∈ D.naut.infG π τ, ∃ k : ℤ, x = (k : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1) τ (s : ℂ), D.naut.infG χ τ = {s} →
    D.naut.infG (D.naut.tw π χ) τ = (D.naut.infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1), D.naut.csd χ → D.naut.csd π →
    D.naut.csd (D.naut.tw π χ)
  infW_alg : ∀ j (W : D.nbc.Wt j) τ, (D.nbc.infW j W τ).Nodup ∧
    ∀ x ∈ D.nbc.infW j W τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2
  infW_inj : ∀ j (W W' : D.nbc.Wt j), D.nbc.infW j W = D.nbc.infW j W' → W = W'
  AU_ext : ∀ j (π π' : D.nbc.AU j),
    (∀ w, IsSplitPl D.host w → D.nbc.locAU j π w = D.nbc.locAU j π' w) →
    (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j π w ∧ D.nbc.sphAU j π' w ∧
      ubc D.R.nV (D.nbc.satAU j π w) = ubc D.R.nV (D.nbc.satAU j π' w)) →
    D.nbc.wtAU j π = D.nbc.wtAU j π' → π = π'

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]

variable (D)

end Formalism.MainNotions.SphericalInertData

end
