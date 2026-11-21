import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Formalism.LocalToGlobal.UnitaryNorms.CharRat
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypChi

noncomputable section

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ChiDRat (D : D7) : Prop := ∀ z : D.Dt, ∃ r : D.what₂.LL, D.what₂.embLL r = ((D.chiD z : ℂˣ) : ℂ)

set_option maxHeartbeats 2000000 in
theorem chRat_ofChiD (h : ChiDRat D) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad} (Y : DetTie S) (c : ℤ)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((DetTw.ofChiD Y c).ch x : ℂˣ) : ℂ) := by
  obtain ⟨r, hr⟩ := h (Y.dt x)
  refine ⟨r ^ c, ?_⟩
  rw [map_zpow₀, hr]
  show _ = (((D.chiD (Y.dt x)) ^ c : ℂˣ) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]

set_option maxHeartbeats 2000000 in
theorem chRat_mem (h : ChiDRat D) {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    ∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = (((formsInMem F dt i hi).tw β).ch (((formsInMem F dt i hi).K β).y cl) : ℂ) := by
  by_cases h' : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h']
    intro β cl
    exact chRat_ofChiD h _ _ _
  · rw [formsInMem_mid F dt i hi (by omega)]
    intro β cl
    exact chRat_ofChiD h _ _ _

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem fillRec (ex : Extra D L hT Gi Gl Kc Dx cX) : ∀ u w hg, FillTie hT u w hg (Gl.Fl u w hg) := by
  intro u w hg v s b hb
  have h1 := ex.fills_all u w hg v s (b + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : wj D (b + 1) (hT.gat_pos u w hg ⟨v, s⟩) = (((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (show b + 1 - 1 < D.R.m by simpa using hb), D.hcW_e]
    rfl
  rw [h2] at h1
  have e : ((((Gl.Fl u w hg).w v (b + 1) s : ℤ) : ℚ) : ℝ) =
      ((wG D.R ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩) (b + 1) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast, h1]
    unfold wG G.kaJ
    push_cast
    ring
  exact Rat.cast_injective e

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

section Gen

variable {L : Type} [Field L] [NumberField L]

theorem ide_snd_mul (a b : Ideles L) (v : HeightOneSpectrum (𝓞 L)) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).2 v = (a : AdeleRing (𝓞 L) L).2 v * (b : AdeleRing (𝓞 L) L).2 v := rfl

end Gen

variable {D : D7}

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end GlobalTheory.Port

end

end
