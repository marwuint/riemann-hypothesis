import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MiStar2OfAnchored
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslatedEvaluationRowsConjLinearBijection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomRelationOfPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorPairForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PostOnMemEEatOfCenter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundIff

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.AtReal

open Formalism.IndefR.Links

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

theorem cols_heq {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    {m : Dc.Mem} {m' : Dc'.Mem} (hm : HEq m m') :
    Dc.a m = Dc'.a m' ∧ (∀ v, HEq (Dc.Xc m v) (Dc'.Xc m' v)) ∧
      ∀ t (x : Fin (Dc.a m) → K) (x' : Fin (Dc'.a m') → K) (F : Fin (Df.nV t) → K) (F' : Fin (Df'.nV t) → K),
        HEq x x' → HEq F F' → Dc.Pt m t x F = Dc'.Pt m' t x' F' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hm
  refine ⟨rfl, fun v => HEq.rfl, fun t x x' F F' hx hF => ?_⟩
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hF
  rfl

theorem cols_mem {Df Df' : DefSide Bs} (hDf : Df = Df') {Dc : DefCols Df} {Dc' : DefCols Df'} (hD : HEq Dc Dc')
    (m : Dc.Mem) : ∃ m' : Dc'.Mem, HEq m m' := by
  subst hDf
  obtain rfl := eq_of_heq hD
  exact ⟨m, HEq.rfl⟩

end Gen

theorem heq_fin {α : Type} {n n' : ℕ} (h : n = n') (x : Fin n → α) : ∃ x' : Fin n' → α, HEq x x' := by
  subst h; exact ⟨x, HEq.rfl⟩

theorem heq_fin' {α : Type} {n n' : ℕ} (h : n = n') (x' : Fin n' → α) : ∃ x : Fin n → α, HEq x x' := by
  subst h; exact ⟨x', HEq.rfl⟩

theorem heq_mat {n n' : ℕ} (h : n = n') (M' : Matrix (Fin n') (Fin n') ℂ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, HEq M M' := by
  subst h; exact ⟨M', HEq.rfl⟩

theorem heq_mulVec {n n' : ℕ} (h : n = n') {M : Matrix (Fin n) (Fin n) ℂ} {M' : Matrix (Fin n') (Fin n') ℂ}
    (hM : HEq M M') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : HEq (M.mulVec x) (M'.mulVec x') := by
  subst h; obtain rfl := eq_of_heq hM; obtain rfl := eq_of_heq hx; rfl

theorem heq_fnorm {n n' : ℕ} (h : n = n') {Y : Matrix (Fin n) (Fin n) ℂ} {Y' : Matrix (Fin n') (Fin n') ℂ}
    (hY : HEq Y Y') {x : Fin n → ℂ} {x' : Fin n' → ℂ} (hx : HEq x x') : fnorm Y x = fnorm Y' x' := by
  subst h; obtain rfl := eq_of_heq hY; obtain rfl := eq_of_heq hx; rfl

theorem heq_cpt {K : Type} [Field K] (σ : K →+* ℂ) {n n' : ℕ} (h : n = n') {x : Fin n → K} {x' : Fin n' → K}
    (hx : HEq x x') : HEq (cpt σ x) (cpt σ x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

theorem heq_cjv (s : Bool) {n n' : ℕ} (h : n = n') {x : Fin n → ℂ} {x' : Fin n' → ℂ}
    (hx : HEq x x') : HEq (Formalism.L2.SG.JoinSI.cjv s x) (Formalism.L2.SG.JoinSI.cjv s x') := by
  subst h; obtain rfl := eq_of_heq hx; rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop.AtReal

end GlobalTheory.MiTop.AtReal

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop

end
