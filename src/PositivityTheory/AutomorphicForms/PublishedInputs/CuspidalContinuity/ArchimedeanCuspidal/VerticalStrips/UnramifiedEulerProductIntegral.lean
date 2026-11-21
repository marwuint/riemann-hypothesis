import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace Ad3.R

def ForF (P : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F], AddChar F Circle → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), IsStd ψ → P F ψ

def Strip (s : ℂ) : Prop := 0 < s.re ∧ s.re < 1

def A1 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (h : GL (Fin 2) F), SB φ →
  SB (fun r => φ (r ᵥ* (h : Matrix (Fin 2) (Fin 2) F))) ∧ SB (sF ψ φ) ∧ (∀ z : ℂ, W2 ψ μ₁ μ₂ (z • φ) = z • W2 ψ μ₁ μ₂ φ) ∧
  ∀ g, W2 ψ μ₁ μ₂ φ (g * h) = ((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2) *
    W2 ψ μ₁ μ₂ (fun r => φ (r ᵥ* (h : Matrix (Fin 2) (Fin 2) F))) g

def A3 : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∃ C : ℂ, C ≠ 0 ∧ ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c →
    ∀ φ₁ φ₃, SB φ₁ → SB φ₃ → ∀ s, Strip s → Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s 1 = C * gam ψ c⁻¹ (1 - s) *
      ∫ p : (Fin 2 → F) × (Fin 2 → F), φ₁ p.1 * conj (φ₃ p.2) * Kr (μ₂ * μ₁⁻¹) c s p.1 ![0, 1] p.2 ∂((m2 ψ).prod (m2 ψ))

def U0 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ (ω : Fˣ →* ℂˣ) (lam : ℂ) (W : GL (Fin 2) F → ℂ),
  Law ψ ω W → TypeT lam W → W 1 = 0 → W = 0

def M1 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnramifiedChar μ₂ →
  1 ≤ quasiCharConductor μ₁ → ∃ φ, SB φ ∧ W2 ψ μ₁ μ₂ φ 1 = 1 ∧ TypeU (μ₁ * μ₂) (quasiCharConductor μ₁)
    ((Real.sqrt (residueCard F) : ℝ) * ((μ₂ (unifUnit F) : ℂˣ) : ℂ)) (W2 ψ μ₁ μ₂ φ)

def M0 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnramifiedChar μ₁ →
  IsUnramifiedChar μ₂ → SB (ind0 : (Fin 2 → F) → ℂ) ∧ W2 ψ μ₁ μ₂ ind0 1 = 1 ∧
    TypeT ((Real.sqrt (residueCard F) : ℝ) * (((μ₁ (unifUnit F) : ℂˣ) : ℂ) + ((μ₂ (unifUnit F) : ℂˣ) : ℂ))) (W2 ψ μ₁ μ₂ ind0)

def E4 : Prop := ForF fun F _ _ _ _ _ _ ψ => ∀ μ₁ μ₂ c : Fˣ →* ℂˣ, IsUnit1 μ₁ → IsUnit1 μ₂ → IsUnit1 c → IsUnramifiedChar μ₁ →
  IsUnramifiedChar μ₂ → IsUnramifiedChar c → ∀ s : ℂ, 0 < s.re → ∀ G : Fˣ → ℂ,
    (∀ a, G a = W2 ψ μ₁ μ₂ ind0 (dg2 a 1) * conj (W2 ψ μ₁ μ₂ ind0 (dg2 a 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1)) →
    (∀ a u : Fˣ, ord (u : F) = 0 → G (a * u) = G a) ∧ (∀ a : Fˣ, G a ≠ 0 → (a : F) ∈ 𝒪[F]) ∧ G 1 = 1 ∧
    (∀ n : ℕ, ‖G (unifUnit F ^ n)‖ ≤ ((n : ℝ) + 1) ^ 2 * (residueCard F : ℝ) ^ (-(n * s.re))) ∧
    (∑' n : ℕ, G (unifUnit F ^ n)) * localLFactor (c * c) (2 * s) = lf3 (μ₁ * μ₂⁻¹) c s * localLFactor c s

def U2 : Prop := ForF fun F _ _ _ _ _ _ _ => ∀ ω : Fˣ →* ℂˣ, Continuous ω → 1 ≤ quasiCharConductor ω → ∀ y : F, ord y = -1 →
  ∃ x d x' d', GammaZeroLevelMembership (quasiCharConductor ω) x d ∧ GammaZeroLevelMembership (quasiCharConductor ω) x' d' ∧ x * uni2 y = uni2 y * x' ∧ ω d ≠ ω d'

def C1 : Prop := ForF fun F _ _ _ _ _ _ _ => (∃ (ϖ : Fˣ) (B : Finset F), Reps ϖ B) ∧ (∀ (ϖ : Fˣ) B, Reps ϖ B → B.card = residueCard F) ∧
  ∀ (ω : Fˣ →* ℂˣ) (n : ℕ) (f : GL (Fin 2) F → ℂ), 1 ≤ n → unitFiltrationUnits F n ≤ ω.ker →
    (∀ x d, GammaZeroLevelMembership n x d → ∀ g, f (g * x) = ((ω d : ℂˣ) : ℂ) * f g) → ∀ ϖ B ϖ' B', Reps ϖ B → Reps ϖ' B' → ∀ x d, GammaZeroLevelMembership n x d → ∀ g : GL (Fin 2) F,
      ∑ b ∈ B, f (g * x * upm ϖ b) = ((ω d : ℂˣ) : ℂ) * ∑ b ∈ B', f (g * upm ϖ' b)

def C0 : Prop := ForF fun F _ _ _ _ _ _ _ => ∀ f : GL (Fin 2) F → ℂ, (∀ x ∈ integralGL F 2, ∀ g, f (g * x) = f g) →
  ∀ ϖ B ϖ' B', Reps ϖ B → Reps ϖ' B' → ∀ x ∈ integralGL F 2, ∀ g : GL (Fin 2) F,
    ∑ b ∈ B, f (g * x * upm ϖ b) + f (g * x * dg2 1 ϖ) = ∑ b ∈ B', f (g * upm ϖ' b) + f (g * dg2 1 ϖ')

def B0 : Prop := (∀ v : Pl, IsStd (localAdelicChar ℚ v) ∧ residueCard (Qv v) = pOf v ∧ (pOf v).Prime ∧
    ord ((pOf v : ℕ) : Qv v) = 1 ∧ (∀ n : ℕ, n ≠ 0 → ord ((n : ℕ) : Qv v) = n.factorization (pOf v)) ∧
    (∀ x, ∃ h, IsLoc2 v x h) ∧ ∀ c : HeckeCharacter ℚ, IsUnit1 (localChar c v)) ∧
  Function.Injective pOf ∧ (∀ p : ℕ, p.Prime → ∃ v, pOf v = p) ∧
  (∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g') ∧
  (∀ (S : Finset Pl) (x : ∀ v : S, Qv v.1), ∃ h, IsUn S x h) ∧ (∃ m, IsK m) ∧
  (∀ g : G2, {v | finAt v g ∉ integralGL (Qv v) 2}.Finite) ∧
  ∀ (v : Pl) (x : Qv v) (a d : (Qv v)ˣ), ∃ (x' : 𝔸[ℚ]) (a' d' : Jd), IsLoc2 v (uni2 x) (uni2 x') ∧ IsLoc2 v (dg2 a d) (dg2 a' d') ∧
    adelicChar ℚ x' = localAdelicChar ℚ v x ∧ (a = d → a' = d') ∧
    ∀ c : HeckeCharacter ℚ, (c.toIdele a' : ℂ) = localChar c v a ∧ (c.toIdele d' : ℂ) = localChar c v d

def D0 : Prop := ∃ 𝓓 : Set Jd, MeasurableSet 𝓓 ∧ (∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓) ∧
  ∀ (τ : ℝ) (M : ℕ), 0 < τ → τ < M → ∫⁻ a in 𝓓, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞

def G0 : Prop := ∃ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓

def G1a : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → μ {g | Dt g = 1} = 0 ∧
  (∀ r : ℝ, 0 < r → ∃ z : Jd, md z ^ 2 = r ∧ ∀ c : HeckeCharacter ℚ, IsOfFinOrder c → c.toIdele z = 1) ∧
  ∀ T : G2 → G2, (T = inv2 ∨ (∃ h, T = fun g => g * h) ∨ ∃ z : Jd, T = fun g => dg2 z z * g) →
    (∀ F : G2 → ℝ≥0∞, Measurable F → LInv F → ∫⁻ g in 𝓕, F (T g) ∂μ = ∫⁻ g in 𝓕, F g ∂μ) ∧
    ∀ F : G2 → ℂ, Measurable F → LInv F → ∫ g in 𝓕, F (T g) ∂μ = ∫ g in 𝓕, F g ∂μ

def G1 : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ F : G2 → ℂ, Continuous F → (∃ C, ∀ g, ‖F g‖ ≤ C) → LInv F →
  (CInv F → ∀ h, ∫ g in 𝓕 ∩ band, F (g * h) ∂μ = ∫ g in 𝓕 ∩ band, F g ∂μ) ∧
  (∀ (η : HeckeCharacter ℚ), IsOfFinOrder η → (∀ (z : Jd) g, F (dg2 z z * g) = (η.toIdele z : ℂ) * F g) → η ≠ 1 →
    ∫ g in 𝓕 ∩ band, F g ∂μ = 0) ∧
  (CInv F → F ≠ 0 → ∫ g in 𝓕 ∩ band, F g * conj (F g) ∂μ ≠ 0)

def G3 : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ H, Aut H → ∀ Φ ∈ Adele2.schwartzBruhat2 ℚ, ∀ σ : ℝ, 1 < σ →
  Measurable (th Φ) ∧ LInv (th Φ) ∧
  ∫⁻ g in 𝓕, (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞

def E1 : Prop := ∀ (S : Finset Pl) (A : ∀ v : S, (Qv v.1)ˣ → ℂ) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (σ : ℝ), 1 < σ →
  (∀ v, Integrable (A v) (multHaar (Qv v.1))) →
  (∀ v ∉ S, (∀ a u : (Qv v)ˣ, ord (u : Qv v) = 0 → G v (a * u) = G v a) ∧ (∀ a, G v a ≠ 0 → (a : Qv v) ∈ 𝒪[Qv v]) ∧ G v 1 = 1 ∧
    ∀ n : ℕ, ‖G v (unifUnit (Qv v) ^ n)‖ ≤ ((n : ℝ) + 1) ^ 2 * (pOf v : ℝ) ^ (-(n * σ))) →
  Multipliable (fun v : {v : Pl // v ∉ S} => ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)) ∧
  ∫ a : Afˣ, (∏ v : S, A v (lf v.1 a)) * ∏ᶠ v : {v : Pl // v ∉ S}, G v.1 (lf v.1 a) ∂finiteIdeleMeasure ℚ =
    (∏ v : S, ∫ a, A v a ∂multHaar (Qv v.1)) * ∏' v : {v : Pl // v ∉ S}, ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)

def E2 : Prop := ∀ (S : Finset Pl) (s : ℂ), 1 < s.re →
  (∀ c : HeckeCharacter ℚ, (∀ v ∉ S, IsUnramifiedChar (localChar c v)) → (∀ v : Pl, v.asIdeal ∣ c.conductor → v ∈ S) ∧
    HasProd (fun v : {v : Pl // v ∉ S} => localLFactor (localChar c v.1) s) (partialLFunction c S s)) ∧
  ∀ ν : ∀ v : Pl, (Qv v)ˣ →* ℂˣ, (∀ v, IsUnit1 (ν v)) → Multipliable fun v : {v : Pl // v ∉ S} => localLFactor (ν v.1) s

def E3 : Prop := ∀ (mK : Measure KA) [mK.IsHaarMeasure] [IsProbabilityMeasure mK] m, IsK m → ∀ (S : Finset Pl)
  (A : ∀ v : S, GL (Fin 2) (Qv v.1) → ℂ), (∀ v, IsLocallyConstant (A v)) →
  ∫ κ : KA, ∏ v : S, A v (finAt v.1 κ.1) ∂mK = ∏ v : S, ∫ κ, A v κ.1 ∂m v.1

def FT : Prop := ∀ γ, IsGauss γ → ∀ (S : Finset Pl) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) →
  tst γ S Ψ ∈ Adele2.schwartzBruhat2 ℚ ∧ sFA (tst γ S Ψ) = tst γ S fun v => sF (localAdelicChar ℚ v.1) (Ψ v)

def H1 : Prop := ∀ (c : HeckeCharacter ℚ) (δ : Bool) (S : Finset Pl), IsOfFinOrder c →
  (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) →
  ∃ L L' : ℂ → ℂ, Differentiable ℂ L ∧ Differentiable ℂ L' ∧
    (∀ s : ℂ, 1 < s.re → L s = (s - 1) * Lp c S s ∧ L' s = (s - 1) * Lp c⁻¹ S s ∧ L' s ≠ 0) ∧
    (∀ s, Strip s → -s * L s * Complex.Gammaℝ (s + if δ then 1 else 0) = (s - 1) * ((if δ then -Complex.I else 1) *
      Complex.Gammaℝ (1 - s + if δ then 1 else 0)) * (∏ v ∈ S, gam (localAdelicChar ℚ v) (localChar c v) s) * L' (1 - s)) ∧
    (c = 1 → L 1 ≠ 0) ∧ (c ≠ 1 → L 1 = 0 ∧ deriv L 1 ≠ 0)

def ForE (P : ∀ (k N : ℕ) [NeZero N], DirichletCharacter ℂ N → (ℕ → ℂ) → HeckeCharacter ℚ → (G2 → ℂ) → Prop) : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ f a, IsForm k N χ f a → IsEig k N χ a →
    ∀ ω φ, Om N χ ω → Lift k N f ω φ → P k N χ a ω φ

def F0 : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ∃ ω, Om N χ ω

def F0b : Prop := ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ (-1) = (-1) ^ k → ∀ ω, Om N χ ω → OmL k N χ ω

def F1 : Prop := ∀ (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) f a, IsForm k N χ f a → a 1 = 1 → ∀ ω, Om N χ ω →
  χ (-1) = (-1) ^ k ∧ ∃ φ, Lift k N f ω φ

def AutomorphicLevelEquivariance : Prop := ForE fun _ N _ _ _ ω φ =>
  (∀ v, ¬ pOf v ∣ N → ∀ x ∈ integralGL (Qv v) 2, ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = φ g) ∧
  (∀ v, pOf v ∣ N → ∀ x d, GammaZeroLevelMembership (N.factorization (pOf v)) x d → ∀ h, IsLoc2 v x h → ∀ g, φ (g * h) = (localChar ω v d : ℂ) * φ g) ∧
  ∀ κ : KA, (∀ w, infAt w κ.1 = 1) → (∀ v, pOf v ∣ N → finAt v κ.1 = 1) → ∀ g, φ (g * κ.1) = φ g

def HeckeSumLocalTranslates : Prop := ForE fun k N _ _ a _ φ => ∀ v (ϖ : (Qv v)ˣ), (ϖ : Qv v) = (pOf v : ℕ) → ∀ (t : ℕ → G2) (t' : G2),
  (∀ b : ℕ, IsLoc2 v (upm ϖ b) (t b)) → IsLoc2 v (dg2 1 ϖ) t' → ∀ x : GL (Fin 2) ℝ, 0 < x.det.val →
    ∑ b ∈ Finset.range (pOf v), φ (realEmb x * t b) + (if pOf v ∣ N then 0 else φ (realEmb x * t')) = lamOf k a v * φ (realEmb x)

def F3 : Prop := ForE fun k N _ _ a ω φ => Hk k N a ω φ

def F2 : Prop := ForE fun k _ _ _ _ ω φ => Continuous (Wh φ) ∧ (∀ x g, Wh φ (uni2 x * g) = (adelicChar ℚ x : ℂ) * Wh φ g) ∧
  (∀ (z : Jd) g, Wh φ (dg2 z z * g) = (ω.toIdele z : ℂ) * Wh φ g) ∧ ∀ t : ℝˣ, Wh φ (realEmb (dg2 t 1)) = WR k t

def F5 : Prop := ForE fun _ _ _ _ _ _ φ => (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ h : G2, (∀ w, infAt w h = 1) → Dec fun g => φ (g * h)

def F4 : Prop := ForE fun k N _ _ a _ _ => ∀ v, pOf v ∣ N → ‖lamOf k a v‖ ^ 2 = pOf v

def E0 : Prop := ForE fun _ N _ _ _ ω φ => ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ g : G2,
  Wh φ g = Wh φ (realEmb (realPart g)) * ∏ᶠ v : Pl, W2 (localAdelicChar ℚ v) (μ₁ v) (μ₂ v) (φ₀ v) (finAt v g)

def X0 : Prop := ForE fun k N _ χ a ω φ => Pure k N χ a → ∀ μ₁ μ₂ φ₀, Mod N ω (Wh φ) μ₁ μ₂ φ₀ → ∀ m, IsK m →
  ∀ (S : Finset Pl), (∀ v, pOf v ∣ N → v ∈ S) → ∀ (c : HeckeCharacter ℚ) (δ : Bool), IsOfFinOrder c →
    (∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1) → (∀ v ∉ S, IsUnramifiedChar (localChar c v)) →
    ∀ (x : ∀ v : S, Qv v.1) (Ψ : ∀ v : S, (Fin 2 → Qv v.1) → ℂ), (∀ v, SB (Ψ v)) → ∃ (C : ℂ) (E E' : ℂ → ℂ), C ≠ 0 ∧
      DifferentiableOn ℂ E {s | 0 < s.re} ∧ DifferentiableOn ℂ E' {s | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → E s = (1 - 2 ^ (1 - s)) * (C * GG k s * ZS m μ₁ μ₂ φ₀ S x Ψ c s *
          ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c v.1) s) * Lp c S s)) ∧
        E' s = (1 - 2 ^ (1 - s)) * (C * GG k s * ZS m μ₁ μ₂ φ₀ S x (fun v => sF (localAdelicChar ℚ v.1) (Ψ v)) c⁻¹ s *
          ((∏' v : {v : Pl // v ∉ S}, lf3 (μ₁ v.1 * (μ₂ v.1)⁻¹) (localChar c⁻¹ v.1) s) * Lp c⁻¹ S s))) ∧
      (∀ s, Strip s → (1 - 2 ^ s) * E s = (1 - 2 ^ (1 - s)) * E' (1 - s)) ∧ (E 1 ≠ 0 → c ≠ 1 → Dih a)

end Ad3.R

end
