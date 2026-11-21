import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TensorMapDescent

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PtId.OneScalar

theorem map_pG_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c c' : Coeff l) (φ : c.F →+* ℂ) (φ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    MvPolynomial.map φ (pG (Dw := Dw) c a n) = MvPolynomial.map φ' (pG (Dw := Dw) c' a n) := by
  have h : ∀ s i hi col, MvPolynomial.map φ (minorPolynomial (Dw := Dw) (n := n) c s i hi col) =
      MvPolynomial.map φ' (minorPolynomial c' s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero, map_zero]

theorem ten_extremal_mem (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    (Formalism.L2.DIV.ten fun τ => extremal K n (lam τ)) ∈ Formalism.L2.DIV.VV K lam :=
  GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.hwMem K n n le_rfl _ (Formalism.L2.DIV.natW_antitone (lam τ))

theorem lt_injective {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (hH : ∀ ρ, tauE D ρ (H.rt : D.host.E) = H.rt0)
    {m n : ℕ} (lt : LtN Dw n → FVar D m n)
    (hlt : ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
      (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))) : Function.Injective lt := by
  have hp : ∀ ℓ : LtN Dw n, ∀ ρ, ℓ.1 = tauE D ρ → (ℓ.2.1 : ℕ) < Dw.p := by
    rintro ⟨σ, s, b⟩ ρ h
    have hs := s.2
    have : Dw.mult σ = Dw.p := by
      rw [show σ = tauE D ρ from h]
      exact if_pos (hH ρ)
    exact this ▸ hs
  intro x y hxy
  obtain ⟨a1, a2⟩ := hlt x
  obtain ⟨b1, b2⟩ := hlt y
  have hpx := hp x (lt x).1
  have hpy := hp y (lt y).1
  rw [hxy] at a1 a2 hpx
  have key : x.1 = y.1 ∧ (x.2.1 : ℕ) = y.2.1 := by
    rcases a2 with ⟨a2, a3⟩ | ⟨a2, a3⟩ <;> rcases b2 with ⟨b2, b3⟩ | ⟨b2, b3⟩
    · exact ⟨a2.trans b2.symm, by omega⟩
    · have := hpx a2; omega
    · have := hpy b2; omega
    · exact ⟨a2.trans b2.symm, by omega⟩
  obtain ⟨σ, s, b⟩ := x
  obtain ⟨σ', s', b'⟩ := y
  obtain ⟨k1, k2⟩ := key
  dsimp only at k1 k2 a1 b1
  subst k1
  obtain rfl : s = s' := Fin.ext k2
  obtain rfl : b = b' := a1.symm.trans b1
  rfl

section Hw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

theorem coefficientMap_extremalTensor_baseChange {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hO : hwOK O.c' (lamV D i) O.hw)
    {c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (hc : CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0') :
    O.c0' O.hw = c0L ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩ := by
  obtain ⟨v', h1, h2⟩ := hc ⟨_, ten_extremal_mem D.what₂.LL (lamV D i)⟩
  rw [← h2]
  congr 1
  apply Subtype.ext
  rw [h1, show (O.hw : Formalism.L2.DIV.Pol O.c'.F D.what₂.Tau (Vc D i).rank) = _ from hO]
  dsimp only
  rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
  simp only [Formalism.L2.DIV.map_extremal]

end Hw

end GlobalTheory.PtId.OneScalar
