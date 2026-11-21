import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugate

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7}

theorem inner_sp {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E) (m : Dc.Mem)
    (c : Fin (Dc.a m) → ℂ) :
    ⟪sEE e, Sp.Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m).op (ramCrd (bR m) c)⟫_ℂ := by
  subst hSp
  obtain rfl := eq_of_heq h
  exact inner_spOf s Dc hK Gd wdD pw bR m _ c

theorem inner_join {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Z : Type}
    {sd : Z → DefSide Bs} (Dcf : ∀ z, DefCols (sd z)) (Spf : ∀ z, SPer (Dcf z)) (z0 z1 : Z) (hz : z0 = z1)
    (Dc : DefCols (sd z1)) (hdc : Dcf z1 = Dc) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hsp : HEq (Spf z1) (spOf s Dc hK Gd wdD pw bR))
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (sEE : E →ₗ⋆[ℂ] (Spf z0).HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc) (e : E)
    (m : (Dcf z0).Mem) (m' : Dc.Mem) (hm : HEq m m') (c : Fin ((Dcf z0).a m) → ℂ) (c' : Fin (Dc.a m') → ℂ)
    (hc : HEq c c') :
    ⟪sEE e, (Spf z0).Pu m (cjv s c)⟫_ℂ = cj s ⟪Tw.out (sEEc e), (pw m').op (ramCrd (bR m') c')⟫_ℂ := by
  subst hz
  subst hdc
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hc
  exact inner_sp s (Dcf z0) hK Gd wdD pw bR (Spf z0) (eq_of_heq hsp) sEE sEEc h e m c

theorem iota_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : GA D (D.sp.Y 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) (x : I.GA) :
    ι.symm x = ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x := by
  subst h
  obtain rfl := eq_of_heq hι
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem op_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) (y : (D.mem u).A.Mu0)
    (T : Cu X u hK) (hT : Formalism.L2.SG.ColDict.colDictL X p.Tr hK T = (y : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    ((p.op y : HHX X) : L2X X) = PuFun X u hK p.Dt T := by
  have hd : (Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  show ((Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin
    ((Formalism.L2.SG.ColDict.colDict X p.Tr hK p.hI p.hB).symm y) : HHX X) : L2X X) = _
  rw [hd]
  rfl

end GlobalTheory.MiTop.PairingL2

namespace GlobalTheory.MiTop.PairingL2

open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned

theorem exists_eval {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))}
    {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St}
    {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ} (hE : EvalTieT M μ 𝓕 E St Gd ι t c)
    (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∀ T : E, ∃ F : L2X St,
      ((F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t (PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ v₀))) ∧
      star F ∈ HHX St ∧ ((sEEofTT M μ 𝓕 E St Gd ι t c T : HHX St) : L2X St) = star F := by
  refine ⟨hE.choose, hE.choose_spec.1, fun T => ⟨(hE.choose_spec.2.choose T : EEC St Gd), ?_, ?_, ?_⟩⟩
  · refine (hE.choose_spec.2.choose_spec T).1.trans (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ι.symm x = (iotaX St h).symm x := iota_symm_eq h ι hι x
    show (T : MMap M) hE.choose (ι.symm x * t) =
      PiTensorProduct.lift (T : MMap M) (PiTensorProduct.tprod ℂ hE.choose) ((iotaX St h).symm x * t)
    rw [h1]
    exact (congrFun (PiTensorProduct.lift.tprod (φ := (T : MMap M)) hE.choose) _).symm
  · exact ((mem_EEC St Gd _).1 (hE.choose_spec.2.choose T).2).1
  · unfold sEEofTT
    simp only [dif_pos hE]
    rfl

theorem inner_smul_star {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (f g : GA D (D.sp.Y 0) → ℂ) (l a : ℂ) (hfg : f = l • g) (F φ P : L2X St)
    (hF : (F : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t f) (hφ : (φ : St.B.I.GA → ℂ) =ᵐ[muX St] evS St h t g)
    (y z : HHX St) (hy : (y : L2X St) = star F) (hz : (z : L2X St) = P) :
    ⟪a • y, z⟫_ℂ = starRingEnd ℂ a * l * ⟪star φ, P⟫_ℂ := by
  have h1 : F = l • φ := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hF, hφ, MeasureTheory.Lp.coeFn_smul l φ] with x h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2, hfg]
    rfl
  have h2 : star (l • φ) = starRingEnd ℂ l • star φ := (Formalism.L2.SG.RowDict.conjL (muX St)).map_smulₛₗ l φ
  rw [inner_smul_left, Submodule.coe_inner, hy, hz, h1, h2, inner_smul_left, starRingEnd_self_apply, mul_assoc]

end GlobalTheory.MiTop.PairingL2

end
