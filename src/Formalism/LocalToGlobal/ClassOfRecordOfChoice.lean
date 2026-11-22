import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.LevelLetterCocycles.TwAllF
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoinP
import Formalism.LocalToGlobal.GroupLattices.ServiceOfTiedSelection
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.LocalToGlobal.Divisibility.RecBridgeTied
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ
import Formalism.SharpRestriction.AdmissibleParameterJoins.DGamMink
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top3

abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

theorem withSm_of_withChN {𝒞 : FamClass} {eps : ℝ} (Fm : FamP eps) (h : WithChN 𝒞 Fm) : WithSm (WithChN 𝒞) Fm :=
  ⟨h, J.dGamSmooth_of_dvd Fm h.2.1⟩

theorem designChoices_upN {𝒞 : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (h : DesignChoices (WithTw 𝒞) C0 cT) :
    DesignChoices (WithTw (WithSm (WithChN 𝒞))) C0 cT := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps he hle K => ?_⟩
  obtain ⟨Fm, CH, C5, Cb, hc, hCH, hL, h5, hb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h eps he hle K
  exact ⟨Fm, CH, C5, Cb, ⟨withSm_of_withChN Fm ⟨hc.1, a8, a10, a6, a7, a13⟩, hc.2⟩, hCH, hL, h5, hb, a1, a2, a3,
    a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

theorem d3_a {C0 : ℝ} {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : D3 C0 𝒜 Fm) : 𝒜 Fm := h.1.1.1.1

theorem closed_eps_le_one (𝒞 : FamClass) : Closed 𝒞 fun {eps} _ _ => eps ≤ 1 := by
  have K : TransportedAlt := by constructor <;> exact 0
  exact ⟨1, one_pos, fun _ _ hle => ⟨K, fun _ _ _ _ => hle⟩⟩

theorem closed_of_mem {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 fun Fm CH => 𝒞 Fm → P Fm CH) :
    Closed 𝒞 P := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, ha, fun e he hle => let ⟨K, hK⟩ := h e he hle; ⟨K, fun Fm CH hc hL => hK Fm CH hc hL hc⟩⟩

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, Formalism.BasicNotions.DV.Used (Fm.D x i) μ

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        Formalism.MainNotions.TwGoodAtAll (Fm.D x i) (Fm.ex x hx i).nch ⟨Formalism.MainNotions.twE Fm x hx i, N0, S⟩

def Duty {eps : ℝ} (Fm : FamP eps) : Prop :=
  PageFix Fm ∧ PageWin Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ TameDistinctF Fm ∧ ChosenWall Fm ∧ TupUsedF Fm ∧ TwAllF Fm

abbrev SelDH (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}

theorem complement_two_of_items {eps : ℝ} {Fm : FamP eps} (h : Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm := by
  obtain ⟨C, x0, h⟩ := Formalism.MainNotions.WeightDegreeSizes.secondComplement_family_of_inputs Fm h
  refine ⟨C, max x0 (Fm.x1 + 1), fun x hx i => h x (le_trans (le_max_left _ _) hx) ?_ i⟩
  have := le_trans (le_max_right _ _) hx
  linarith

section ColChoice

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

structure ColChoice (P : Formalism.L2.Rows.RowSideFamily ex) where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : Formalism.L2.DIV.ColRec3 (Formalism.L2.DIV.fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.SPer (c.face Zs)
  tie : Formalism.L2.DIV.ColTie3 P X e c Sp

end ColChoice

end Formalism.L2.Top3

end
