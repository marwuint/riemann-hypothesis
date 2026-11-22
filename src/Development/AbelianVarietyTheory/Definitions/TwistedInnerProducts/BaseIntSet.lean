import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsLevDatHalfLatInd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Tow

variable {D : D7}

abbrev lat (E : ExpSet D) : AddSubgroup (WO E.V E.W) := latO E.V E.W E.ΛV E.ΛW fun _ => True

def badN (D : D7) : ℕ := D.host.QS * D.host.q * Ideal.absNorm D.host.ccK

section Core

variable (T : CoreJ D) (j : ℕ) (E : ExpSet D) (hW : T.V j T.σ₀ = E.W) (hr : E.W.rank = D.R.r) (w : WeightFamilies.Wt D j)

def iotaE : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin E.W.rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j

def muE (dd : GA D E.W → ℂ) : GA D E.W → ℂ := fun g => castDict hW (T.mu j T.σ₀) g * dd g

structure IsTw (ph : ℂ) (dd : GA D E.W → ℂ) (N : ℕ) (C : Cover T j T.σ₀) : Prop where
  unif : C.IsUnif
  emb : C.σ₂ = inC C.d.c₂
  pd : C.d.pd = E.pde 0 * E.pde 1 * N
  half : ∀ PP ∈ E.Pd, C.d.I ≤ PP.asIdeal
  curve : GlobalTheory.CompRat.CurveOver T.Q.H C.d.c₂.F C.d.l₂.M
  dict : IsDict C.U₂ E.W hr (castDict hW C.dict₂) (iotaE T j E hr) (T.x₀ j T.σ₀)
  frame : FrameTie C.U₂ E.W hr (T.x₀ j T.σ₀) E.sW E.BW
  cc : CcIs E.θ E.V E.W hr C.U₂ (castDict hW C.dict₂) (muE T j E hW dd) (T.x₀ j T.σ₀) E.om E.f₀ fun k => ph * C.cc₂ k

variable (lt : LtN (T.Q.Dw j) E.V.rank ≃ FVar D E.W.rank E.V.rank)

variable {O : Type} [CommRing O] (C : CoefLat E O)

end Core

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure ReadsAt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)
    (E : ExpSet D) : Prop where
  V : E.V = Vc D i
  W : E.W = Wc D i
  ψ : E.ψ = R.ψ
  θ : E.θ = R.θ
  sW : HEq E.sW (cart (R.MW i (sg0 D A)))
  BW : HEq E.BW (onb (R.MW i (sg0 D A)))
  ΛV : HEq E.ΛV (R.ΛV i)
  ΛW : HEq E.ΛW (R.ΛW i)
  χV : E.χV = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1
  χW : E.χW = (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2
  om : HEq E.om (R.ωP i t)
  f₀ : HEq E.f₀ (R.vacP i)
  gp : E.gp = D.host.g
  Pg : E.Pg = R.Pg
  Pd : E.Pd = R.Q t
  pde : E.pde = ![D.host.pde, D.host.pde']

end Real

end GlobalTheory.Tow

end
