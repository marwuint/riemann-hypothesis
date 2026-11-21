import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CuspFamily

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

structure CptOrigin (Y : Model Xo c β) (S₀ : Finset ℕ) (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) where

  𝔐 : HodgeCpt Y S₀ Dc.y

  deg : ℕ
  cover : 𝔐.IsCover deg

  bg : CMType H → CMType H ⊕ CMType H

  sm : CMType H → CMType H ⊕ CMType H
  side : (bg = Sum.inl ∧ sm = Sum.inr ∧ Dc.j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ Dc.j = D.q)
  N_eq : Dc.N = D.p + D.q

  i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li
  i_inj : ∀ τ, Function.Injective (i τ)
  i_range : ∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)
  F_eq : ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ)
  lat : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat
  bd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → (w ∈ Dc.Bd ↔ ¬ 𝔐.Interior z)
  metric : ∀ τ a (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → 𝔐.Interior z →
    InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => i τ ((Dc.h τ).b a k)) ((Dc.h τ).gram a w)
  S_disj : Disjoint Dc.S S₀
  R_ge : ∀ p ∈ Dc.S, 4 ≤ 𝔐.R p
  tors : ∀ p ∈ Dc.S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)
  ht_vb : ∀ p ∈ Dc.S, ∀ s, (𝔐.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre 𝔐.ξ r q} (labelRk D s)
    (𝔐.Vgen s)
  vert : ∀ p ∈ Dc.S, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord Dc.y) ch q →
    ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li)
      (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
      (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) →
      (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y ch (-Dc.vdeg p)))

section Ranks

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd)

theorem CptOrigin.rk_bg (τ : CMType H) : labelRk D (Or.bg τ) = Dc.j := by
  rcases Or.side with ⟨h, -, hj⟩ | ⟨h, -, hj⟩ <;> simp [h, hj]

theorem CptOrigin.rk_sm (τ : CMType H) : labelRk D (Or.sm τ) = Dc.N - Dc.j := by
  rcases Or.side with ⟨-, h, hj⟩ | ⟨-, h, hj⟩ <;> simp [h, hj, Or.N_eq]

theorem CptOrigin.bg_ne_sm (τ τ' : CMType H) : Or.bg τ ≠ Or.sm τ' := by
  rcases Or.side with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> simp [h, h']

include Or in

theorem CptOrigin.n_eq : Dc.n = Fintype.card (CMType H) * D.p * D.q := by
  rcases Or.side with ⟨-, -, hj⟩ | ⟨-, -, hj⟩ <;> simp [ComponentData.n, hj, Or.N_eq]
  ring

end Ranks

namespace Origin

open GroundTheory.Heights₂.Heights.NineStatements

section Period

variable {Ψ : Type} [Fintype Ψ] {V : Ψ → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)]
  {Dc : ComponentData II Ψ K J Ω V} {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

def IsPeriodAt (C : CuspDataOn Dc T O' Lt) (w : (Σ k, J k) → ℂ) {g : ℕ} (P : Lt → Fin g → ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (B : O' → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  (∀ (a : O') v, P (a • v) = (B a).mulVec (P v)) ∧
  (∀ v, C.normSq w v = (P v ⬝ᵥ Hm.mulVec (star (P v))).re) ∧
  (∀ v v', ((C.form v v' : ℤ) : ℝ) = (P v ⬝ᵥ Hm.mulVec (star (P v'))).im) ∧
  ∃ pr : Ψ → (Fin g → ℂ) → Fin g → ℂ,
    (∀ τ x, (∀ a, (B a).mulVec (pr τ x) = C.emb τ a • pr τ x) ∧
      ∀ x', (∀ a, (B a).mulVec x' = C.emb τ a • x') → (x - pr τ x) ⬝ᵥ Hm.mulVec (star x') = 0) ∧
    ∀ τ v v', star (C.lie w τ v) ⬝ᵥ C.lie w τ v' = pr τ (P v') ⬝ᵥ Hm.mulVec (star (pr τ (P v)))

theorem isPeriodAt_restrict (C : CuspDataOn Dc T O' Lt) (h : T' ⊆ T) (w : (Σ k, J k) → ℂ) {g : ℕ} (P : Lt → Fin g → ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (B : O' → Matrix (Fin g) (Fin g) ℂ) :
    IsPeriodAt (C.restrict h) w P Hm B ↔ IsPeriodAt C w P Hm B := Iff.rfl

end Period

end Origin

section Comparison₂

open GroundTheory.Heights₂.Heights.NineStatements

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd) {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

def CptOrigin.CuspTieAt (e : 𝓞 E ≃+* O') (C : CuspDataOn Dc T O' Lt) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X)
    (w : (Σ k, J k) → ℂ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ Or.𝔐.t.G.left) (g : ℕ)
    (u : HolUnif A (Or.𝔐.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ)
    (B : O' → Matrix (Fin g) (Fin g) ℂ) (α : Lt ≃+ u.Λ),
    IsGrpPullback A Or.𝔐.t.G z φ ∧ u.IsAH Hm χ ∧
    (∀ a x, (u.ex ((B (e a)).mulVec x)).left ≫ φ = (u.ex x).left ≫ φ ≫ (Or.𝔐.t.act.act a).left) ∧
    (∀ τ a, ValAt Or.𝔐.ξ z (Or.𝔐.emb (Or.sm τ) a) (C.emb τ (e a))) ∧
    Origin.IsPeriodAt C w (fun v => (α v : Fin g → ℂ)) Hm B

variable {Or}

theorem CptOrigin.cuspTieAt_restrict (e : 𝓞 E ≃+* O') (C : CuspDataOn Dc T O' Lt) (h : T' ⊆ T)
    (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) :
    Or.CuspTieAt e (C.restrict h) z w ↔ Or.CuspTieAt e C z w := Iff.rfl

end Comparison₂

end GlobalTheory.CompanionTheory.Ar
