import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

noncomputable section

namespace PI.VolFromSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section SW

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))

def SWa1 : Prop :=
  AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 => μ 𝓕 < ⊤

end SW

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def ratIn (K : Subgroup (HA (AF F) σ J)) : Subgroup K :=
  ((HFinIn (AF F) σ J) ⊓ K).subgroupOf K

def IsOmT (ψ : AddChar (AF F) ℂ) {a : ℕ} (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) : Prop :=
  νX {X | gramR (AF F) σ J X ≠ T.map (inclR (AF F))} = 0 ∧
  AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) a) fun μinf =>
  AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) a) fun νinf =>
  AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) fun μv =>
  AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a) =>
    ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) fun νv =>
  AllSome (fun fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E) =>
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf) fun fibInf =>
  AllSome (fun fibV : ∀ v : HeightOneSpectrum (𝓞 F),
      HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) fun fibV =>
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
    (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
    Integrable Φ νX ∧
    Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ T hT))) ∧
    ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ T hT))) *
      ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ T hT))

def IsCompatT {a : ℕ} (X0 : Fin a → Fin M → E) (μ : Measure (HA (AF F) σ J))
    (μ' : Measure (stabT (AF F) σ J X0)) (νX : Measure (Fin a → Fin M → AF F ⊗[F] E)) : Prop :=
  νX {y | ¬ ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y} = 0 ∧
  ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
    ∀ s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J,
      (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) → s y • ratTup (AF F) X0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX

def VolStabAt {a : ℕ} (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j) : Prop :=
  AllSome (IsCharAF F) fun ψ =>
  AllSome (IsHaarH F E σ M J) fun μ =>
  AllSome (IsOmT F E σ M J ψ (gramE σ J X0) hT) fun νX =>
  AllSome (fun μ' : Measure (stabT (AF F) σ J X0) =>
    μ'.IsHaarMeasure ∧ IsCompatT F E σ M J X0 μ μ' νX) fun μ' =>
  AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
  AllSome (fun 𝓕' : Set (stabT (AF F) σ J X0) =>
    IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕' μ') fun 𝓕' =>
    μ' 𝓕' = μ 𝓕

end Ext

def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J

end PI.VolFromSW
