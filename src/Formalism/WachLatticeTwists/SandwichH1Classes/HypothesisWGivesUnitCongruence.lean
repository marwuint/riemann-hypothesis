import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForEveryTwist

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

structure Lat (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] (r : ℕ) where
  ρ : G → Matrix (Fin r) (Fin r) ℤ_[ℓ]
  one : ρ 1 = 1
  mul : ∀ g h, ρ (g * h) = ρ h * ρ g

structure HypWc (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg → Matrix (Fin r) (Fin r) ℤ_[ℓ]) (En : Set (Matrix (Fin r) (Fin r) ℤ_[ℓ]))
    (πs ξ : As) (M0 h0 : ℕ) where

  Xx : Matrix (Fin r) (Fin r) WC

  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1

  fixH : ∀ h ∈ H, Xx.map (act h) * ((ρ h).map (algebraMap ℤ_[ℓ] WC)) = Xx

  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx

  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P

  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ g).map (algebraMap ℤ_[ℓ] WC)) = ((Gm g).map jA).map ι * Xx

  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}

  W4 : ∀ E ∈ En, ∃ E' : Matrix (Fin r) (Fin r) As,
    Xx * E.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

structure Setup (ℓ : ℕ) [Fact ℓ.Prime] where

  Tt : TateTr ℓ

  As : Type

  AA : Type

  WC : Type

  OC : Type
  [cAs : CommRing As]
  [cAA : CommRing AA]
  [cWC : CommRing WC]
  [cOC : CommRing OC]
  [aAA : Algebra ℤ_[ℓ] AA]
  [aWC : Algebra ℤ_[ℓ] WC]
  [aOC : Algebra ℤ_[ℓ] OC]
  [tOC : TopologicalSpace OC]
  [trOC : IsTopologicalRing OC]
  [csOC : ContinuousConstSMul ℤ_[ℓ] OC]
  jA : As →+* AA
  ι : AA →+* WC
  φ : WC →+* WC

  ϑ : AA →+* OC

  ϑs : As →+* Tt.Om
  emb : Tt.Oi →+* OC

  Gg : Type
  [gGg : Group Gg]

  G : Type
  [gG : Group G]
  [tG : TopologicalSpace G]
  p : G →* Gg

  Hs : Subgroup Gg

  H : Subgroup G
  act : Gg →* (WC ≃+* WC)
  actA : Gg →* (AA ≃+* AA)
  actO : Gg →* (OC ≃ₐ[ℤ_[ℓ]] OC)
  χ : Gg →* ℤ_[ℓ]ˣ
  πs : As
  ξ : As
  x : As

  cx : Gg → As

  γ : Gg

  σ : As →+* As

  gg : G

  z : Tt.Om
  z' : Tt.Om

  ϖ : Tt.Om
  ϖ₁ : Tt.Om

  ϖ' : Tt.Om
  c : OC
  s : ℕ

attribute [instance] Setup.cAs Setup.cAA Setup.cWC Setup.cOC Setup.aAA Setup.aWC Setup.aOC Setup.tOC Setup.trOC
  Setup.csOC Setup.gGg Setup.gG Setup.tG

namespace Setup

variable {ℓ : ℕ} [Fact ℓ.Prime] (R : Setup ℓ)

def w : ℤ_[ℓ]ˣ := R.χ (R.p R.gg)

structure Facts (r M0 h0 : ℕ) : Prop where
  lemA : LemmaAProp R.ι R.φ r
  injι : Function.Injective R.ι
  injj : Function.Injective R.jA
  phix : R.φ (R.ι (R.jA R.x)) = R.ι (R.jA R.x * R.jA R.ξ)
  xinzd : ∀ a : R.WC, R.ι (R.jA R.ξ) * a = 0 → a = 0
  thx : (R.ϑ (R.jA R.x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * R.c = (ℓ : R.OC)
  eqι : ∀ g a, R.ι (R.actA g a) = R.act g (R.ι a)
  eqϑ : ∀ g a, R.ϑ (R.actA g a) = R.actO g (R.ϑ a)
  actZ : ∀ g (t : ℤ_[ℓ]), R.act g (algebraMap ℤ_[ℓ] R.WC t) = algebraMap ℤ_[ℓ] R.WC t
  algι : ∀ t : ℤ_[ℓ], R.ι (algebraMap ℤ_[ℓ] R.AA t) = algebraMap ℤ_[ℓ] R.WC t
  algϑ : ∀ t : ℤ_[ℓ], R.ϑ (algebraMap ℤ_[ℓ] R.AA t) = algebraMap ℤ_[ℓ] R.OC t
  gx : ∀ g, R.actA g (R.jA R.x) = R.jA (R.cx g) * R.jA R.x
  gσ : ∀ a, R.actA R.γ (R.jA a) = R.jA (R.σ a)
  embϑ : ∀ a, R.emb (algebraMap R.Tt.Om R.Tt.Oi (R.ϑs a)) = R.ϑ (R.jA a)
  lnzd : ∀ a : R.OC, (ℓ : R.OC) * a = 0 → a = 0
  σ1 : ∀ a, R.σ a - a ∈ Ideal.span {(ℓ : R.As), R.πs}
  σ2 : ∀ a ∈ Ideal.span {(ℓ : R.As), R.πs}, R.σ a - a ∈ (Ideal.span {(ℓ : R.As), R.πs}) ^ 2
  ϑπ : R.ϑs R.πs = R.ϖ'
  dv' : R.ϖ' ∣ (ℓ : R.Tt.Om)
  zz : R.z * R.z' = algebraMap ℤ_[ℓ] R.Tt.Om (ℓ : ℤ_[ℓ])
  ϖϖ : R.ϖ * R.ϖ₁ = algebraMap ℤ_[ℓ] R.Tt.Om (ℓ : ℤ_[ℓ])
  dvd : R.z * R.ϖ ∣ R.ϖ' ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0)))
  pg : R.p R.gg = R.γ ^ (ℓ ^ (R.s + n0 ℓ (M0 + h0) + 1))
  fixx : R.actO (R.p R.gg) (R.ϑ (R.jA R.x)) = R.ϑ (R.jA R.x)
  s1 : 1 ≤ R.s
  s2 : ℓ = 2 → 2 ≤ R.s
  valγ : PadicInt.valuation ((R.χ R.γ : ℤ_[ℓ]) - 1) = R.s
  omtf : ∀ a : R.Tt.Om, (ℓ : ℤ_[ℓ]) • a = 0 → a = 0

end Setup

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
