import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.PrinLevClass

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

def evV {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) :
    MvPolynomial (Vm D.what₂.Tau N) ℚ →ₐ[ℚ] MvPolynomial M.Z.LB ℚ :=
  aeval (fun v => match v with
    | Sum.inl r => X (rt r)
    | Sum.inr (false, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x l) ^ k) + ∑ l, X (M.omW.x l) ^ k)
    | Sum.inr (true, k) => C ((Nat.factorial k : ℚ)⁻¹) *
        ((∑ l, X (M.lieW.x' l) ^ k) + ∑ l, X (M.omW.x' l) ^ k))

def evC {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) : M.Z.Ch :=
  evQ M.Z (evV M rt G)

def toR {σ : Type} (G : MvPolynomial σ ℚ) : MvPolynomial σ ℝ := map (algebraMap ℚ ℝ) G

def dRt (Tau : Type) [Fintype Tau] (N : ℕ) (r : Rt Tau N) : MvPolynomial (Vm Tau N) ℝ :=
  X (Sum.inl (false, r)) - X (Sum.inl (true, r))

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

end Formalism.MainNotions.LatticeTransfer

end
