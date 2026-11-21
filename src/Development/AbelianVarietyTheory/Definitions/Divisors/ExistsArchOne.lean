import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsMulNe
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ArchAtEmptyOfRhoZero
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeOfDet
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZeros
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZeros
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

def sub (M : TwoLevels E r U C) (H : Subgroup U) : TwoLevels E r H C :=
  { M with
    tr := fun u c => M.tr u c
    tr_herm := fun u => M.tr_herm u
    tr_Λ := fun u => M.tr_Λ u
    tr_L' := fun u => M.tr_L' u
    tr_conj := fun u => M.tr_conj u
    tr_mul := fun u v => M.tr_mul u v
    tr_faithful := fun u c h1 h2 => Subtype.ext (M.tr_faithful u c h1 h2) }

def IsPullRep (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la)) : Prop :=
  ∃ a : U → C → ℂˣ, ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS la) (c : C) (x : M.dom),
    ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp la) : C → M.dom → ℂ) c x = (a h c : ℂ) * M.pull h F c x.1

def Ranks (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (s : ℕ) (ep c : ℝ) : Prop :=
  Module.Finite ℂ (M.cusp ka) ∧ Module.Finite ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) ∧
    (1 - ep) * finrank ℂ (M.cusp ka) ≤ finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    (finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 s)) : ℝ) ≤ c * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s)) ∧
    Module.Finite ℂ (M.cusp (ka - deMul M.Ψ r M.p0 s))

def ArchOne (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ Xa : ArchInM X, Xa.L = L ∧ Xa.Fp = Fp ∧ Xa.T = T ∧ GlobalTheory.Shares.Margins X Xa ∧ Nonempty (FlatM X Xa)

def ArchOn (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (T : ℕ) : Prop :=
  ∃ L Fp : Wt M.Ψ r, ka = Fp + T • L ∧ GapsGe M.p0 L 1 ∧ PairGe L (1.9 * T) ∧
    GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 ∧ PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 ∧
    ∀ c, ArchOne (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T

def sOf (M : TwoLevels E r U C) : ℕ := 2 * r + 50 * r ^ 2 * M.dimX + 2

theorem even_sOf (M : TwoLevels E r U C) : Even (sOf M) := ⟨r + 25 * (r ^ 2 * M.dimX) + 1, by unfold sOf; ring⟩

theorem le_sOf (M : TwoLevels E r U C) : 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ sOf M := Nat.le_succ _

theorem sOf_sub (M : TwoLevels E r U C) (H : Subgroup U) : sOf (sub M H) = sOf M := rfl

theorem cusp_sub (M : TwoLevels E r U C) (H : Subgroup U) (la : Wt M.Ψ r) : (sub M H).cusp la = M.cusp la := rfl

end Model

section Point

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def HalfUnip (H : Subgroup p.P.Gp) : Prop :=
  ∃ k : Fin 2, ∀ g ∈ H, ∀ v : D.nd.PlG k,
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) g ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))

def ModelAt (T : ℕ) : Prop :=
  ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
    (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
    IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
    (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ ∧
    (∀ H, HalfUnip p H → LevelHyp (sub M H)) ∧ M.Ψ.card = D.R.f ∧
    ((M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ ArchOn M ka T))

def ShareW (y : ℝ) : Prop :=
  (1 - y) * (p.R.toRealDat.nW i : ℝ) ≤ (Nat.card p.P.P0 : ℝ) * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

def BadW (del : ℝ) : Prop :=
  (finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL _) : ℝ) ≤
    del * finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)

end Point

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

end GlobalTheory.ShareOn

end
