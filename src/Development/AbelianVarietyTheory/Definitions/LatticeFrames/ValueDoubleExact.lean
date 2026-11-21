import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

structure PairDat (p : ι → SplitPt D k) (A S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  α : ∀ i, Frame (p i) A n
  α₀ : ∀ i, Frame (p i) S (n ⊕ Fin 1)
  P : ι → Pair k n

structure MidDat (p : ι → SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] where
  β : ∀ i, Frame (p i) S n
  Q : ι → Pair k n

variable {p : ι → SplitPt D k} {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
  [DecidableEq n'']

def PairDat.Ram {A S : HSp D} (a : PairDat p A S n) (φ : GA D A → ℂ) : Prop := IsContAut A φ ∧ ∀ i, RamAt (a.α i) (a.P i) φ

def PairDat.sAll {A S : HSp D} (a : PairDat p A S n) (q : Unif k) (χ : ι → AddChar 𝓀[k] ℂ) (ε : ι → 𝓀[k]ˣ) (l : List ι)
    (φ : GA D A → ℂ) : GA D A → ℂ :=
  l.foldr (fun i ψ => sOp (a.α i) (a.P i) q (χ i) (ε i) ψ) φ

def OverAll (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S)
    (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (l : List ι) (f f' : WO S T → ℂ) : Prop :=
  l.foldr (fun i (r : (WO S T → ℂ) → Prop) f₂ => ∃ g, r g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f₂) (fun f₂ => f₂ = f) f'

structure DblLat {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) where
  L₀ : Lat B.V
  M₀ : Lat B.V₀
  L₁ : Lat J.W
  M₁ : Lat J.W₀
  L₂ : Lat B'.V
  M₂ : Lat B'.V₀

structure DblShape {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (Λ : DblLat B J B') (P : Pl D → Prop) (q : Unif k) (a : PairDat p B.A B.V₀ n')
    (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n'') : Prop where
  inj : Function.Injective fun i => (p i).v
  mem : ∀ i, P (p i).v
  good : ∀ v, P v → GoodBF ψ B J Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ v
  adapt : ∀ v, P v → AdaptFB ψ J B' Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v
  unr : ∀ v, P v → UnrAt s₁ v ∧ UnrAt s₂ v
  split : ∀ v, P v → (∀ i, v ≠ (p i).v) → SplitCore B' Λ.M₂ v
  gl : ∀ i, GluedCore B Λ.M₀ q (a.α i) (a.α₀ i) (a.P i)
  gl' : ∀ i, GluedCore B' Λ.M₂ q (a'.α i) (a'.α₀ i) (a'.P i)
  mid : ∀ i, (b.β i).IsLat Λ.M₁ (b.Q i).lat

def ShiftLaw (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (x : Mx D W.rank ρ)
    (P : Pl D → Prop) (𝔉 : (WO V W → ℂ) → (WO V₀ W₀ → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ V W f → ∀ N : Mx D ρ ρ, MxAt P N → (∀ i j, j ≤ i → N i j = 0) →
    𝔉 (heisO ψ V W (dV.extX W (x ⬝ N)) f) = psiE ψ (upSum N) • 𝔉 f

def FlatShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), ShiftLaw ψ B.d (xZero J.d) P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B),
      ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) P (flatFB s)

def SupportShift (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W)
    (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatFB s (· = v) 𝔉 → ShiftLaw ψ J.d (xLast B.d (vecB B.o B.ζ)) (· = v) 𝔉 → ∀ f, Vac ψ J.W B.V LV LW (· = v) f →
      Vac ψ J.W₀ B.V₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt B.V (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) ∧ ∃ γ ∈ grpAt B.V₀ (· = v), ∃ κ, InK B.V LW (· = v) κ ∧
          h = n * B.d.emb0 γ * κ ∧ ∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ LW₀ (· = v) →
            mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ LW₀ (· = v)

def InBig (S : HSp D) (R : Subgroup (GA D S)) (L : Lat S) (P : Pl D → Prop) (h : GA D S) : Prop :=
  ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

def SuppFirst (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (P : Pl D → Prop), (∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) →
    (∀ v, P v → UnrAt s v) → IsSelfDualC J.W LW → ∀ Φ, Vac ψ B.V J.W LV LW P Φ →
      (∀ κ κ', InK B.V LV P κ → InK J.W LW P κ' → s.om (κ, κ') Φ = Φ) ∧
      ∀ g ∈ grpOff B.V P, (∀ h, flatBF s (s.om (g, h) Φ) ≠ 0 → InBig J.W (jacGrp J.d) LW P h) ∧
        ∀ h ∈ grpOff J.W P, Vac ψ B.V₀ J.W₀ LV₀ LW₀ P (flatBF s (s.om (g, h) Φ))

def SuppSecond (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n'']
    [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1))
    (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Λ : DblLat B J B') (P : Pl D → Prop) (a : PairDat p B.A B.V₀ n') (b : MidDat p J.W₀ n) (a' : PairDat p B'.A B'.V₀ n''),
    DblShape s₁ s₂ Λ P q a b a' → IsSelfDualC B'.V Λ.L₂ → ∀ Φ₁ Φ₂, Vac ψ B.V J.W Λ.L₀ Λ.L₁ P Φ₁ → Vac ψ J.W B'.V Λ.L₁ Λ.L₂ P Φ₂ →
      (∀ κ κ', InK J.W Λ.L₁ P κ → InK B'.V Λ.L₂ P κ' → s₂.om (κ, κ') Φ₂ = Φ₂) ∧
      ∀ h₁ ∈ grpOff J.W P, (∀ h₂ ∈ grpOff B'.V P, Vac ψ J.W₀ B'.V₀ Λ.M₁ Λ.M₂ P (flatFB s₂ (s₂.om (h₁, h₂) Φ₂))) ∧
        ∀ g ∈ grpOff B.V P, ∀ φ, a.Ram φ → ∀ h₂, Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ ≠ 0 →
          InBig B'.V (besGrp B'.d B'.o) Λ.L₂ P h₂

def AllBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ)
    (n : Type) [Fintype n] [DecidableEq n] (A S : HSp D) (a : PairDat p A S n), Function.Injective (fun i => (p i).v) →
    ∀ I : List ι, Set.BijOn (a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I) {φ | a.Ram φ} {φ | a.Ram φ} ∧
      ∃ c c' : GA D A →₀ ℂ, (∀ g, c g ≠ 0 ∨ c' g ≠ 0 → g ∈ grpAt A fun v => ∃ i, v = (p i).v) ∧
        (∀ φ, a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I φ = c.sum fun g x => x • rTrans g φ) ∧
        ∀ φ, a.Ram φ → a.Ram (c'.sum fun g x => x • rTrans g φ) ∧
          a.sAll q (fun i => resChar (χ i) (hχ i) q) ε I (c'.sum fun g x => x • rTrans g φ) = φ

theorem SplitPt.sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b := by
  have h : ∀ a, p.e * p.sec a = p.sec a := fun a => by rw [← p.sec_pr, p.pr_sec]
  have h2 := p.sec_pr (p.sec a * p.sec b)
  rwa [map_mul, p.pr_sec, p.pr_sec, ← mul_assoc, h] at h2

theorem SplitPt.sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

def SplitPt.idele (p : SplitPt D k) : kˣ →* (AE D)ˣ :=
  Units.map
    { toFun := fun a => 1 + p.sec (a - 1)
      map_one' := by rw [sub_self, map_zero, add_zero]
      map_mul' := fun a b => by
        rw [show a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) by ring, map_add, map_add, p.sec_mul]
        ring }

theorem SplitPt.idele_val (p : SplitPt D k) (a : kˣ) : (p.idele a : AE D) = 1 - p.e + p.sec a := by
  change 1 + p.sec (a - 1) = _
  rw [map_sub, p.sec_one]
  ring

variable (k) in

def sgnRes (s : ℤˣ) : 𝓀[k]ˣ := Units.map (Int.castRingHom 𝓀[k]).toMonoidHom s

end GlobalTheory.FinPl

end
