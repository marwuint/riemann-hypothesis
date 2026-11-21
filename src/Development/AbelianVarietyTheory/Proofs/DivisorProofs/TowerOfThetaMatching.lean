import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageConstantTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomFramesChangeStageZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

theorem gbig_and {Q₁ Q₂ : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) : GBig (fun G μ C x b => Q₁ G μ C x b ∧ Q₂ G μ C x b) := by
  obtain ⟨F1, h1⟩ := h₁
  obtain ⟨F2, h2⟩ := h₂
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G =>
    ⟨k1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hμ G,
      k2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hμ G⟩⟩

theorem gbig_mono {Q₁ Q₂ : GP} (h : GBig Q₁)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → Q₁ G μ₀ C x b → Q₂ G μ₀ C x b) : GBig Q₂ := by
  obtain ⟨F, h⟩ := h
  refine ⟨F, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, k⟩ := h ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ hμ (k C hC D large₂ he hx hR T Lc μ₀ hμ G)⟩

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem isAwayUnit_inv {m : ℕ} {x : K} (h : GlobalTheory.Square.IsAwayUnit m x) (hx : x ≠ 0) : GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨b, hb⟩, e⟩ := h
  refine ⟨(m : 𝓞 K) ^ k * b, k', k + k', ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e2 : ((m : 𝓞 K) : K) ^ k' = (a : K) * (b : K) := by
    rw [← map_pow, hb]; push_cast; ring
  have e3 : ((m : 𝓞 K) : K) = (m : K) := by simp
  rw [e3] at e2
  rw [e2, ← e]
  push_cast
  field_simp

theorem stepRatio_self {T' : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T') (cc qq : T' → ℕ) (x : ℂ) :
    GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq x x :=
  ⟨1, fun _ => 1, fun _ => 1, GlobalTheory.Square.IsAwayUnit.one Qn, fun _ _ => ⟨one_dvd _, one_dvd _⟩, by simp⟩

theorem stepRatio_div {T' : Type} {σ₀ : K →+* ℂ} {Qn : ℕ} {S0 : Finset T'} {cc qq : T' → ℕ} {y y₀ : ℂ}
    (h : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq y y₀) (h₀ : y₀ ≠ 0) : GlobalTheory.Square.StepRatio σ₀ Qn S0 cc qq (y / y₀) 1 := by
  obtain ⟨b, g, g', hb, hg, e⟩ := h
  exact ⟨b, g, g', hb, hg, by rw [e, mul_div_assoc, div_self h₀]⟩

end Units

section Descent

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil} {μ₀ : T}

def FacIn (W : G.Weil) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), IsStageC W i j p q X →
  ∃ lam : T → ℂ, Factor X W.ψ W.θ lam

def SmallIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def BigIn (W : G.Weil) (μ₀ : T) : Prop := ∀ (i j : Fin D.R.m) (p : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ)
  (e : ℕ) (Lf : T → ℂ → ℂ), IsStageC W i j (p + 1) 0 X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
    (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
      IsStageC W i j p 0 Y ∧ Y.IsConst W.ψ W.θ c ∧ (∀ t, y t ≠ 0 ∧ lam t = y t * Lf t (e : ℂ) * c t) ∧
      ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀)

def cons (y : T → ℂ) (u : ℕ → T → ℂ) : ℕ → T → ℂ
  | 0 => y
  | k + 1 => u k

theorem cons_zero (y : T → ℂ) (u : ℕ → T → ℂ) : cons y u 0 = y := rfl

theorem cons_succ (y : T → ℂ) (u : ℕ → T → ℂ) (k : ℕ) : cons y u (k + 1) = u k := rfl

theorem descent (hF : FacIn W) (hs : SmallIn W μ₀) (hb : BigIn W μ₀) (i j : Fin D.R.m) (Lf : T → ℂ → ℂ)
    (hL : ∀ t, IsHeckeL (nuH G t i j) (Lf t)) :
    ∀ (q p e : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) (c : T → ℂ), IsStageC W i j p q X → X.IsConst W.ψ W.θ c →
      A.rank = A'.rank + 2 * e → p ≤ e →
      ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (cY : T → ℂ) (u : ℕ → T → ℂ) (κ : ℂ),
        IsStageC W i j 0 0 Y ∧ Y.IsConst W.ψ W.θ cY ∧ κ ≠ 0 ∧ (∀ k t, u k t ≠ 0 ∧ GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (u k t) (u k μ₀)) ∧
        ∀ t, c t * ∏ k ∈ range q, Lf t ((e + k + 1 : ℕ) : ℂ) =
          κ * (∏ k ∈ range (p + q), u k t) * cY t * ∏ k ∈ range p, Lf t ((e + q - k : ℕ) : ℂ) := by
  intro q
  induction q with
  | zero =>
    intro p
    induction p with
    | zero =>
      intro e A A' WW X c hX hc _ _
      refine ⟨A, A', WW, X, c, fun _ _ => 1, 1, hX, hc, one_ne_zero, fun k t => ⟨one_ne_zero, stepRatio_self _ _ _ _ _ _⟩,
        fun t => by simp⟩
    | succ p ih =>
      intro e A A' WW X c hX hc he hpe
      obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
      obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
      obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hb i j p A A' WW X lam e Lf hX hl he hL
      have hr : B.rank = B'.rank + 2 * (e - 1) := by
        obtain ⟨-, -, a1, a2, -⟩ := hX
        obtain ⟨-, -, b1, b2, -⟩ := hY
        omega
      obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih (e - 1) Y cY' hY hcY' hr (by omega)
      refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
        fun k t => ?_, fun t => ?_⟩
      · rcases k with _ | k
        · exact ⟨(hy t).1, hyr t⟩
        · exact hu k t
      · have h1 := hid t
        have h2 := (hy t).2
        simp only [range_zero, prod_empty, mul_one, add_zero] at h1 ⊢
        simp only [prod_range_succ', cons_succ, cons_zero, Nat.sub_zero]
        have e3 : ∏ k ∈ range p, Lf t ((e - (k + 1) : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e - 1 - k : ℕ) : ℂ) :=
          prod_congr rfl fun k _ => by rw [show e - (k + 1) = e - 1 - k by omega]
        rw [e3, e1 t]
        linear_combination κ₁ * h2 + (κ₁ * y t * Lf t (e : ℂ)) * h1
  | succ q ih =>
    intro p e A A' WW X c hX hc he hpe
    obtain ⟨lam, hl⟩ := hF i j _ _ A A' WW X hX
    obtain ⟨κ₁, hκ₁, e1⟩ := hl.eq_mul hc
    obtain ⟨B, B', W₁, Y, cY', y, hY, hcY', hy, hyr⟩ := hs i j p q A A' WW X lam e Lf hX hl he hL
    have hr : B.rank = B'.rank + 2 * (e + 1) := by
      obtain ⟨-, -, a1, a2, -⟩ := hX
      obtain ⟨-, -, b1, b2, -⟩ := hY
      omega
    obtain ⟨B₂, B₂', W₂, Y₂, cY, u, κ, hY₂, hcY, hκ, hu, hid⟩ := ih p (e + 1) Y cY' hY hcY' hr (by omega)
    refine ⟨B₂, B₂', W₂, Y₂, cY, cons y u, κ₁ * κ, hY₂, hcY, mul_ne_zero hκ₁ hκ,
      fun k t => ?_, fun t => ?_⟩
    · rcases k with _ | k
      · exact ⟨(hy t).1, hyr t⟩
      · exact hu k t
    · have h1 := hid t
      have h2 := (hy t).2
      rw [show p + (q + 1) = p + q + 1 by omega]
      simp only [prod_range_succ', cons_succ, cons_zero]
      have e3 : ∏ k ∈ range q, Lf t ((e + (k + 1) + 1 : ℕ) : ℂ) = ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (k + 1) + 1 = e + 1 + k + 1 by omega]
      have e4 : ∏ k ∈ range p, Lf t ((e + (q + 1) - k : ℕ) : ℂ) = ∏ k ∈ range p, Lf t ((e + 1 + q - k : ℕ) : ℂ) :=
        prod_congr rfl fun k _ => by rw [show e + (q + 1) - k = e + 1 + q - k by omega]
      simp only [add_zero] at e3 ⊢
      rw [e3, e4, e1 t]
      linear_combination (κ₁ * ∏ k ∈ range q, Lf t ((e + 1 + k + 1 : ℕ) : ℂ)) * h2 + (κ₁ * y t) * h1

end Descent

end GlobalTheory.SqTower

namespace GlobalTheory.SqTower

end GlobalTheory.SqTower
