import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

def idV (𝔞 : FI D) (v : Pl D) : AddSubgroup (AE D) :=
  AddSubgroup.closure {y | ∃ α ∈ intAf D.host.F, (∀ w, w ≠ v → evalV D.host.F w α = 0) ∧ ∃ a ∈ 𝔞,
    y = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] a}

def dI (D : D7) : FI D := FractionalIdeal.spanSingleton _ D.host.xi0 * D.host.AA * D.host.AAbar

def cI (D : D7) (j : ℕ) : FI D :=
  FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (j / 2)) * (D.host.AA * D.host.AAbar⁻¹) ^ ((D.R.m - j) / 2)

def MonoId {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D) : Prop :=
  MonoAt d L L₀ v ∧ ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a ∈ idV (𝔟 i) v

def LineId {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV (vecB o ζ) ∈ latV S M (· = v) ↔ a ∈ idV 𝔠 v

def LineLatAt (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (LL : Lat L) (v : Pl D) : Prop :=
  ∀ a ∈ idAt D (· = v), a • ratV ζ ∈ latV L LL (· = v) ↔ a ∈ idV 𝔠 v

variable {a : XPart D u}

structure YPart.Sk (b : YPart a) (ζ₀ : Fin a.Lz.rank → D.host.E)
    (τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E) : Prop where
  base : (a.dat b).Base
  chBF : ∀ j ρ h, (b.sBF j ρ h).χV = a.c.chS (j + 1) ∧ (b.sBF j ρ h).χW = a.c.chT (j + 1)
  chFB : ∀ j σ h, (b.sFB j σ h).χV = a.c.chS (j + 1 + 1) ∧ (b.sFB j σ h).χW = a.c.chT (j + 1 + 1)
  norm : ∀ j ρ h, (star (b.bes j ρ h).ζ ⬝ᵥ (b.bes j ρ h).L.gram *ᵥ (b.bes j ρ h).ζ) *
    (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E)
  tau : ∀ j h, τ j h *ᵥ ζ₀ = D.host.xi0 ^ (D.R.m / 2) • (b.bes j 0 h).ζ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {o : OffX a k ι} {b : YPart a}

structure CoreLat (o : OffX a k ι) (b : YPart a)
    (β₀ : ∀ j ρ h i, Frame (o.p i) (b.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)) (M : ∀ j ρ h, Lat (b.bes j ρ h).V₀) : Prop where
  sd : ∀ j ρ h, IsSelfDualC _ (M j ρ h)
  glued : ∀ j ρ h i, GluedCore ((a.dat b).B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i)
  split : ∀ j ρ h, ∃ LL, IsSelfDualC (b.bes j ρ h).L LL ∧ ∀ v, ¬ o.atT v →
    LineLatAt _ (b.bes j ρ h).ζ (cI D j) LL v ∧ OrthAt (b.bes j ρ h).o (M j ρ h) (a.x j).L LL v
  line : ∀ j ρ h v, LineId (b.bes j ρ h).o (b.bes j ρ h).ζ (M j ρ h) (cI D j) v

theorem idV_mono {𝔞 𝔟 : FI D} (h : 𝔞 ≤ 𝔟) (v : Pl D) : idV 𝔞 v ≤ idV 𝔟 v := by
  apply AddSubgroup.closure_mono
  rintro y ⟨α, hα, hv, x, hx, rfl⟩
  exact ⟨α, hα, hv, x, h hx, rfl⟩

theorem idV_zero (v : Pl D) : idV (0 : FI D) v = ⊥ := by

  rw [idV, AddSubgroup.closure_eq_bot_iff]
  rintro y ⟨α, -, -, x, hx, rfl⟩
  obtain rfl : x = 0 := by simpa using hx
  simp

end GlobalTheory.SeeSaw

end
