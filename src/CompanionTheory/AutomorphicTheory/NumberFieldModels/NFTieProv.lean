import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.StatementTL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge

namespace Formalism.MainStatements.NFTie

noncomputable section

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def GaugeQQ (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), FamR P Bs Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
      MA.toSm P (rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (rawR P Bs.μsec e Φ ρ')) ρ

def tr (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)

end defs

structure GenRel {A A' : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Ring A'] [StarRing A'] [Algebra ℂ A'] {r : ℕ}
    (Rl : Subalgebra ℂ (A × A')) (L : R.LevelData A r) (st : Fr.Start A) (L' : R.LevelData A' r) (st' : Fr.Start A') :
    Prop where
  p : ∀ l, (L.p l, L'.p l) ∈ Rl ∧ (star (L.p l), star (L'.p l)) ∈ Rl
  c : ∀ l, (L.c l, L'.c l) ∈ Rl ∧ (star (L.c l), star (L'.c l)) ∈ Rl
  ci : ∀ l, (L.ci l, L'.ci l) ∈ Rl ∧ (star (L.ci l), star (L'.ci l)) ∈ Rl
  ζ : (L.ζ, L'.ζ) ∈ Rl
  ζi : (L.ζi, L'.ζi) ∈ Rl
  ζb : (L.ζb, L'.ζb) ∈ Rl
  ζbi : (L.ζbi, L'.ζbi) ∈ Rl
  GG : (L.GG, L'.GG) ∈ Rl
  GGi : (L.GGi, L'.GGi) ∈ Rl
  QQ : ∀ Y : ℂ, star Y = Y → ∀ a b, (st.QQ Y a b, st'.QQ Y a b) ∈ Rl
  xi : ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → Y ∈ st'.inv → (st.xi Y, st'.xi Y) ∈ Rl

end

end Formalism.MainStatements.NFTie
