import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.RealPins

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

def Anchored (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ)
    (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  ∀ u, ∃ p b : ℂ, p ≠ 0 ∧ b ≠ 0 ∧ ∀ t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    c u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) * b =
      p * ⟪sEE (V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def UnitAt (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ) : Prop :=
  (∀ u t, c u t ≠ 0) ∧ ∀ u w (k : K), Bs.v0.embedding k = c u (X.μ w) / c u Bs.μ0 → vw w k = 0

end Alg

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

abbrev rJ : Set (GA D (D.sp.Y 0)) :=
  levS (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

abbrev rChi : GA D (D.sp.Y 0) → ℂ :=
  Formalism.IndefR.Lev.levChi (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))

def rowOf (e : W.Q.Rl.HE.H) : SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) := PiTensorProduct.lift (W.Q.Rl.HE.e e)

def rowAt (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    SmT (W.Q.Rl.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ) :=
  rowOf W (W.Q.Rl.Th t (W.Q.Rl.jX t (W.Q.F.eV (cxW W).zs t F)))

abbrev F0 (u : D.what₂.Word) : Formalism.L2.Forms.Forms0 D u := (W.R.T.cols.forms u).to0

structure BotDat (u : D.what₂.Word) where
  B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)
  b : GA D (D.sp.Y 0)
  a₀ : GA D (D.sp.X 0)
  a : GA D (D.sp.X 0)
  k : GA D (D.sp.Y 0)

variable {W}

structure BotDat.Pin {u : D.what₂.Word} (d : BotDat W u) (z : GA D (D.sp.Y 0)) : Prop where
  adapted : d.B.Adapted (W.S.tr u).wt
  h0 : IsTransportAdelicCorrection (W.S.tr u) d.a₀
  fin : d.a ∈ GfC (D.sp.X 0)
  cen : d.a ∈ Subgroup.center (GA D (D.sp.X 0))
  lev : d.k ∈ rJ W
  eq : embA d.B.d d.B.o (d.a₀ * d.a) * d.b =
    (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * d.k)

variable (W)

structure BotHyp : Prop where
  hyp : HypAt W
  pins : RealPins W.Q
  see : SeeEx W.Q
  used : ∀ t : W.P.T, Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t)
  idE : GlobalTheory.Core.Mi.IdE W.S.X
  gap : GlobalTheory.Count.GapGe W.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  fin : Formalism.L2.SG.PackageTie2.FinX W.S.Y

end GlobalTheory.MiTop

namespace GlobalTheory.MiTop

def PuNZ (D : D7) : Prop :=
  ∀ u, ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0

end GlobalTheory.MiTop

end
