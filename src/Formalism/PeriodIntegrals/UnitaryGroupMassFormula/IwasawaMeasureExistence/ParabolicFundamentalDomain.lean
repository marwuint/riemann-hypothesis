import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwaStmt

noncomputable section

namespace PI.IwaMeasEx.Sk

open MeasureTheory
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
  Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

section Data

variable {X : CData} {J : ℕ} (D : BaseDatum X.I J)

structure PK (μK : Measure X.I.GA) : Prop where
  univ : μK Set.univ = 1
  supp : μK (D.kZero : Set X.I.GA)ᶜ = 0
  inv : ∀ k ∈ D.kZero, μK.map (fun x => k * x) = μK

variable (c : Composition J)

def wgt (m : X.I.GA) : ℝ≥0∞ := ENNReal.ofReal (PI.IwaMeasEx.dInv D.toWittFrame c m)

def muP (μN μM : Measure X.I.GA) : Measure X.I.GA :=
  (μN.prod (μM.withDensity (wgt D c))).map (fun q => q.1 * q.2)

structure PN (μN : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μN
  ne : μN ≠ 0
  supp : μN (D.toWittFrame.uniA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μN s ≠ ⊤
  inv : ∀ n ∈ D.toWittFrame.uniA c, μN.map (fun x => n * x) = μN
  modl : ∀ m ∈ D.toWittFrame.leviA c, μN.map (fun x => m * x * m⁻¹) = wgt D c m • μN

structure PM (μM : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μM
  ne : μM ≠ 0
  supp : μM (D.toWittFrame.leviA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μM s ≠ ⊤
  inv : ∀ m ∈ D.toWittFrame.leviA c, μM.map (fun x => m * x) = μM

def IntF (μK μP : Measure X.I.GA) (cIw : ℝ≥0∞) : Prop :=
  cIw ≠ 0 ∧ cIw ≠ ⊤ ∧ ∀ Φ : X.I.GA → ℝ≥0∞, Measurable Φ →
    ∫⁻ x, Φ x ∂(X.I.muA X.μf) = cIw * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP

def NF : Subgroup X.I.GA := PPF X.I (D.toWittFrame.flag c) ⊓ D.toWittFrame.uniA c

def MF : Subgroup X.I.GA := PPF X.I (D.toWittFrame.flag c) ⊓ D.toWittFrame.leviA c

def FdP (μN μM : Measure X.I.GA) (FN FM Om : Set X.I.GA) : Prop :=
  MeasurableSet FN ∧ MeasurableSet FM ∧ MeasurableSet Om ∧
    IsFundamentalDomain (PPF X.I (D.toWittFrame.flag c)) Om (muP D c μN μM) ∧
    (∀ n ∈ D.toWittFrame.uniA c, ∀ m ∈ D.toWittFrame.leviA c, n * m ∈ Om ↔ n ∈ FN ∧ m ∈ FM) ∧
    IsFundamentalDomain (NF D c) FN μN ∧ IsFundamentalDomain (MF D c) FM μM

def LeviP (μM : Measure X.I.GA) (FM : Set X.I.GA) (VM : ℝ≥0∞) : Prop :=
  ∀ Φ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Φ →
    ∫⁻ m in FM, Φ (PI.IwaMeasEx.tBlk D.toWittFrame c m) ∂μM =
      VM * ∫⁻ t in posO c.length, Φ t * ∏ i, ENNReal.ofReal (t i)⁻¹

end Data

end PI.IwaMeasEx.Sk

end
