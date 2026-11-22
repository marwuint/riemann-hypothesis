import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FactorDepth

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ}

def PolyBetween (la : PointsOfFlagModel.abelian₂ p c) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
    ∀ (Ch : IntegralChartA3 Xo c T io y) (k : ℕ),
      (A : EReal) ≤ nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ∧
        nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (MvPolynomial.map io P) ≤ (B : EReal)

variable (l) in

def HalfSplit (g g' : ℕ) (π π' : 𝓞 E) : Prop :=
  g.Prime ∧ g'.Prime ∧ g ≠ g' ∧ l.M = g' * g ∧ π * H.bar π = (g : 𝓞 E) ∧ π' * H.bar π' = (g' : 𝓞 E) ∧
    l.Mb = Ideal.span {π * π'} ∧ GlobalTheory.PtTie.SplitsIn E g ∧ GlobalTheory.PtTie.SplitsIn E g'

theorem HalfSplit.symm {g g' : ℕ} {π π' : 𝓞 E} (h : HalfSplit l g g' π π') : HalfSplit l g' g π' π := by
  obtain ⟨a, b, c, d, e, f, i, j, k⟩ := h
  exact ⟨b, a, c.symm, d.trans (mul_comm _ _), f, e, by rw [i, mul_comm], k, j⟩

end Free

def JetNum (D : D7) (dF : ℕ) (cst : ℝ) : Prop :=
  ∀ k, 4 * dF + 4 ≤ D.host.g k ∧ (dF : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < D.host.g k ∧
    GlobalTheory.PtTie.rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 * ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (dF : ℝ) ^ 2) / D.host.g k ≤ cst

end GlobalTheory.RefSum

end
