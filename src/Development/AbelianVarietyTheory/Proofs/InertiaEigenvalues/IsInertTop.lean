import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SingleDatum

variable {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H}

def IsHalfIdem (l : Geo.Tor.Level H) (e : AE D) : Prop :=
  ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ l.Mb ≤ PP.asIdeal

def levPoint (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D)
    (q : Fin V.rank → LevQ Dw l) : WO V W :=
  Matrix.of fun a b => e * incA D (ι (cSep l • levRep (q b)) a / (l.M : D.host.E))

def transSum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D) (f₀ : WO V W → ℂ) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    WO V W → ℂ :=
  ((Nat.card (Fin V.rank → LevQ Dw l) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l, w q • heisO ψ V W (levPoint V W l ι e q) f₀

def VacPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ) : Prop :=
  IsPair ψ θ V W χV χW om ∧ V.rank ≠ 0 ∧ (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V ∧
    (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W ∧ IsSelfDualC V ΛV ∧ IsSelfDualC W ΛW ∧
    (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) ∧
    (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧
    IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀

def clsScal (χ : (AE D)ˣ →* Circle) (y : (AE D)ˣ) {n : ℕ} (Λ : GenLat D.host.E n) (r : ℕ) : ℂ :=
  ((χ y : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E n).toAddSubgroup.addSubgroupOf
    Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)⁻¹

variable (Dw) in

def IsLetters {m n : ℕ} (lt : LtN Dw n ≃ FVar D m n) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))

variable (Dw) in

def degA (a : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : D.host.E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

variable {l : Geo.Tor.Level H} {Xo : Moduli Dw l}

def IsDict {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  IsUnf U ∧ GlobalTheory.Member.IotaOK Dw W ι ∧ (∀ k, IsMod W hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictLat U W hr dict ι e F ik φ th x₀

def FrameTie {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s ∧
    ∀ hq : (U.X k).p0 + Dw.p = r, IsBasOf W hr (U.X k) hq (fun τ => x₀ τ.1) BW

def IsThetaSum {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂)
    (w : T → (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat D.host.E n) (N : ℕ) (P : T → MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
      (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
      evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t

def intOf (A : ValuationSubring ℂ) (K : Subfield ℂ) : Subring ℂ := A.toSubring ⊓ K.toSubring

end GlobalTheory.SingleDatum

end
